"""Finite checks of the two round-two corollaries, independent of the Lean proof."""
from itertools import combinations, product


def test_status_at_each_reachable_set():
    # Search for actual total left inverses of each concrete observation map.
    for number_of_outputs in range(4):
        outputs = range(number_of_outputs)
        for count in range(number_of_outputs + 1):
            for reachable in combinations(outputs, count):
                models = [
                    (reachable, dict(zip(reachable, reachable))),
                    (tuple(product(reachable, (0, 1))),
                     {pair: pair[0] for pair in product(reachable, (0, 1))}),
                ]
                statuses = []
                for states, observation in models:
                    assert set(observation.values()) == set(reachable)
                    statuses.append(any(
                        all(decoder[observation[x]] == x for x in states)
                        for decoder in product(states, repeat=number_of_outputs)
                    ))
                expected = [True, False] if reachable else [not outputs] * 2
                assert statuses == expected


def test_joint_measurement_separates_target_values():
    # All binary reports, readings and targets on four source states.
    states = range(4)
    binary_maps = tuple(product((0, 1), repeat=len(states)))
    for report, reading, target in product(binary_maps, repeat=3):
        separates = all(
            reading[x] != reading[y]
            for x, y in combinations(states, 2)
            if report[x] == report[y] and target[x] != target[y]
        )
        # The pair of bits indexes one of four joint observation labels.
        labels = tuple(2 * report[x] + reading[x] for x in states)
        can_recover = any(
            all(decoder[labels[x]] == target[x] for x in states)
            for decoder in binary_maps
        )
        assert can_recover == separates
