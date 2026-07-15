import Mathlib

set_option autoImplicit false

/-!
# Boundary-Limited Observer Systems

This file develops the initial formal core of a boundary-limited
observer framework.

The formal results establish the following claims:

1. An underlying state is mapped to an observer-accessible state.
2. Distinct underlying states may produce the same observation.
3. Quantities accessible through the interface must agree on those states.
4. A non-injective observation map cannot possess a globally exact decoder.
5. No test using only observer-accessible information can distinguish
   observationally equivalent states.
6. Generative models with the same accessible observations produce the
   same possible outcomes under every admissible experiment.
7. A finite observation space smaller than the underlying state space
   necessarily collapses at least two distinct underlying states.

These results do not prove the single-observer metaphysical hypothesis.
-/

universe u v w u₁ u₂ u₃

namespace BoundaryObserver

/-!
## Observer interfaces
-/

/--
An observer interface maps an underlying world state into an
observer-accessible observation.
-/
structure ObserverInterface (World : Type u) where
  Obs : Type v
  observe : World → Obs

/--
Two underlying states are observationally equivalent relative to `I`
when they produce exactly the same accessible observation.
-/
def ObsEq
    {World : Type u}
    (I : ObserverInterface World)
    (x y : World) : Prop :=
  I.observe x = I.observe y

/--
Every state is observationally equivalent to itself.
-/
@[refl]
theorem obsEq_refl
    {World : Type u}
    (I : ObserverInterface World)
    (x : World) :
    ObsEq I x x := by
  rfl

/--
Observational equivalence is symmetric.
-/
@[symm]
theorem obsEq_symm
    {World : Type u}
    (I : ObserverInterface World)
    {x y : World}
    (hxy : ObsEq I x y) :
    ObsEq I y x := by
  exact hxy.symm

/--
Observational equivalence is transitive.
-/
@[trans]
theorem obsEq_trans
    {World : Type u}
    (I : ObserverInterface World)
    {x y z : World}
    (hxy : ObsEq I x y)
    (hyz : ObsEq I y z) :
    ObsEq I x z := by
  exact hxy.trans hyz

/-!
## Interface-accessible quantities
-/

/--
A quantity `q` is accessible through the interface when it can be
computed entirely from the accessible observation.

Equivalently, `q` factors through the observation map.
-/
def FactorsThrough
    {World : Type u}
    (I : ObserverInterface World)
    {Value : Type w}
    (q : World → Value) : Prop :=
  ∃ qbar : I.Obs → Value, q = qbar ∘ I.observe

/--
Any quantity that factors through the interface is constant on each
observational-equivalence class.
-/
theorem factorized_quantity_respects_obsEq
    {World : Type u}
    (I : ObserverInterface World)
    {Value : Type w}
    (q : World → Value)
    (hq : FactorsThrough I q)
    {x y : World}
    (hxy : ObsEq I x y) :
    q x = q y := by
  rcases hq with ⟨qbar, hfactor⟩
  rw [hfactor]
  exact congrArg qbar hxy

/-!
## Exact reconstruction
-/

/--
A globally exact decoder reconstructs every underlying state from its
accessible observation.

The decoder is therefore a left inverse of the observation map.
-/
def HasExactDecoder
    {World : Type u}
    (I : ObserverInterface World) : Prop :=
  ∃ decode : I.Obs → World,
    Function.LeftInverse decode I.observe

/--
If a globally exact decoder exists, then the observation map is
injective.
-/
theorem exact_decoder_implies_injective
    {World : Type u}
    (I : ObserverInterface World)
    (hdecoder : HasExactDecoder I) :
    Function.Injective I.observe := by
  rcases hdecoder with ⟨decode, hleft⟩
  exact Function.LeftInverse.injective hleft

/--
If the observation map is not injective, then no globally exact
decoder can exist.
-/
theorem no_exact_decoder_of_not_injective
    {World : Type u}
    (I : ObserverInterface World)
    (hNotInjective : ¬ Function.Injective I.observe) :
    ¬ HasExactDecoder I := by
  intro hdecoder
  apply hNotInjective
  exact exact_decoder_implies_injective I hdecoder

/-!
## Internal tests
-/

/--
An internal binary test receives only an observer-accessible
observation.
-/
abbrev InternalTest
    {World : Type u}
    (I : ObserverInterface World) :=
  I.Obs → Bool

/--
No internal test can distinguish two underlying states that produce
the same accessible observation.
-/
theorem internal_test_cannot_distinguish_obsEq
    {World : Type u}
    (I : ObserverInterface World)
    (test : InternalTest I)
    {x y : World}
    (hxy : ObsEq I x y) :
    test (I.observe x) = test (I.observe y) := by
  exact congrArg test hxy

/-!
## Generative models and experimental indistinguishability

Two models may possess different latent state spaces while producing
the same set of observer-accessible observations.

When this occurs, no experiment restricted to accessible observations
can distinguish the models through its possible outcomes.
-/

/--
A generative model consists of a latent state space and a map from
latent states to observer-accessible observations.
-/
structure GenerativeModel (Obs : Type u₂) where
  Latent : Type u₁
  observe : Latent → Obs

/--
An observation is reachable under a model when at least one latent
state produces it.
-/
def Produces
    {Obs : Type u₂}
    (M : GenerativeModel Obs)
    (o : Obs) : Prop :=
  ∃ x : M.Latent, M.observe x = o

/--
Two generative models are observationally equivalent when they
produce exactly the same observer-accessible observations.

Their latent state spaces do not need to be identical.
-/
def ModelObsEq
    {Obs : Type u₂}
    (M N : GenerativeModel Obs) : Prop :=
  ∀ o : Obs, Produces M o ↔ Produces N o

/--
Every model is observationally equivalent to itself.
-/
@[refl]
theorem modelObsEq_refl
    {Obs : Type u₂}
    (M : GenerativeModel Obs) :
    ModelObsEq M M := by
  intro o
  rfl

/--
Observational equivalence between models is symmetric.
-/
@[symm]
theorem modelObsEq_symm
    {Obs : Type u₂}
    {M N : GenerativeModel Obs}
    (hMN : ModelObsEq M N) :
    ModelObsEq N M := by
  intro o
  exact (hMN o).symm

/--
Observational equivalence between models is transitive.
-/
@[trans]
theorem modelObsEq_trans
    {Obs : Type u₂}
    {M N K : GenerativeModel Obs}
    (hMN : ModelObsEq M N)
    (hNK : ModelObsEq N K) :
    ModelObsEq M K := by
  intro o
  exact (hMN o).trans (hNK o)

/--
An admissible experiment receives only observer-accessible
information and returns an experimental result.
-/
abbrev AdmissibleExperiment
    (Obs : Type u₂)
    (Result : Type u₃) :=
  Obs → Result

/--
A result is possible under a model when some latent state produces an
observation that causes the experiment to return that result.
-/
def ExperimentCanProduce
    {Obs : Type u₂}
    {Result : Type u₃}
    (M : GenerativeModel Obs)
    (experiment : AdmissibleExperiment Obs Result)
    (result : Result) : Prop :=
  ∃ x : M.Latent, experiment (M.observe x) = result

/--
If two models produce exactly the same accessible observations, every
admissible experiment has exactly the same possible results under both
models.
-/
theorem modelObsEq_preserves_experiment_results
    {Obs : Type u₂}
    {Result : Type u₃}
    (M N : GenerativeModel Obs)
    (hMN : ModelObsEq M N)
    (experiment : AdmissibleExperiment Obs Result)
    (result : Result) :
    ExperimentCanProduce M experiment result ↔
      ExperimentCanProduce N experiment result := by
  constructor
  · rintro ⟨x, hx⟩
    have hMProduces : Produces M (M.observe x) := by
      exact ⟨x, rfl⟩
    have hNProduces : Produces N (M.observe x) :=
      (hMN (M.observe x)).mp hMProduces
    rcases hNProduces with ⟨y, hy⟩
    refine ⟨y, ?_⟩
    calc
      experiment (N.observe y) =
          experiment (M.observe x) := congrArg experiment hy
      _ = result := hx
  · rintro ⟨y, hy⟩
    have hNProduces : Produces N (N.observe y) := by
      exact ⟨y, rfl⟩
    have hMProduces : Produces M (N.observe y) :=
      (hMN (N.observe y)).mpr hNProduces
    rcases hMProduces with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    calc
      experiment (M.observe x) =
          experiment (N.observe y) := congrArg experiment hx
      _ = result := hy

/--
Boolean-test specialization of model-level experimental
indistinguishability.
-/
theorem modelObsEq_preserves_test_acceptance
    {Obs : Type u₂}
    (M N : GenerativeModel Obs)
    (hMN : ModelObsEq M N)
    (test : Obs → Bool) :
    ExperimentCanProduce M test true ↔
      ExperimentCanProduce N test true := by
  exact modelObsEq_preserves_experiment_results M N hMN test true

/-!
## Finite interfaces and unavoidable information loss

When the underlying state space contains more states than the
observer-accessible state space, the observation map cannot be
injective.

This is a finite pigeonhole obstruction. At least two distinct
underlying states must produce the same accessible observation.
-/

/--
A finite observation interface with fewer accessible states than
underlying states cannot be injective.
-/
theorem finite_interface_not_injective_of_card_lt
    {World : Type u}
    [Fintype World]
    (I : ObserverInterface World)
    [Fintype I.Obs]
    (hCard : Fintype.card I.Obs < Fintype.card World) :
    ¬ Function.Injective I.observe := by
  intro hInjective
  have hCardLe : Fintype.card World ≤ Fintype.card I.Obs :=
    Fintype.card_le_of_injective I.observe hInjective
  omega

/--
If a finite observation space is smaller than the underlying state
space, then two distinct underlying states produce the same
observation.
-/
theorem finite_interface_has_collision
    {World : Type u}
    [Fintype World]
    (I : ObserverInterface World)
    [Fintype I.Obs]
    (hCard : Fintype.card I.Obs < Fintype.card World) :
    ∃ x y : World, x ≠ y ∧ ObsEq I x y := by
  classical
  have hNotInjective : ¬ Function.Injective I.observe :=
    finite_interface_not_injective_of_card_lt I hCard
  by_contra hNoCollision
  apply hNotInjective
  intro x y hObservation
  by_contra hDistinct
  exact hNoCollision ⟨x, y, hDistinct, hObservation⟩

/--
A finite observation interface with fewer accessible states than
underlying states cannot possess a globally exact decoder.
-/
theorem finite_interface_has_no_exact_decoder
    {World : Type u}
    [Fintype World]
    (I : ObserverInterface World)
    [Fintype I.Obs]
    (hCard : Fintype.card I.Obs < Fintype.card World) :
    ¬ HasExactDecoder I := by
  exact no_exact_decoder_of_not_injective I
    (finite_interface_not_injective_of_card_lt I hCard)

/--
Every internal binary test assigns the same result to at least one
pair of distinct underlying states whenever the observation space is
strictly smaller than the underlying state space.
-/
theorem finite_interface_has_indistinguishable_pair
    {World : Type u}
    [Fintype World]
    (I : ObserverInterface World)
    [Fintype I.Obs]
    (hCard : Fintype.card I.Obs < Fintype.card World)
    (test : InternalTest I) :
    ∃ x y : World,
      x ≠ y ∧ test (I.observe x) = test (I.observe y) := by
  rcases finite_interface_has_collision I hCard with
    ⟨x, y, hDistinct, hObservation⟩
  refine ⟨x, y, hDistinct, ?_⟩
  exact congrArg test hObservation

/--
Every interface-accessible quantity assigns the same value to at
least one pair of distinct underlying states whenever the observation
space is strictly smaller than the underlying state space.
-/
theorem finite_interface_accessible_quantity_collision
    {World : Type u}
    [Fintype World]
    (I : ObserverInterface World)
    [Fintype I.Obs]
    {Value : Type w}
    (q : World → Value)
    (hq : FactorsThrough I q)
    (hCard : Fintype.card I.Obs < Fintype.card World) :
    ∃ x y : World, x ≠ y ∧ q x = q y := by
  rcases finite_interface_has_collision I hCard with
    ⟨x, y, hDistinct, hObservation⟩
  refine ⟨x, y, hDistinct, ?_⟩
  exact factorized_quantity_respects_obsEq I q hq hObservation

/-!
## Observable quotient and canonical boundary representation

The observational quotient identifies underlying states exactly when
they produce the same observer-accessible observation.

The quotient therefore represents the distinctions that survive the
observer interface. Distinctions erased by the interface are not
represented as distinct quotient states.
-/

/--
The observable quotient is the underlying world state space modulo
the kernel of the observation map.
-/
abbrev ObservableQuotient
    {World : Type u}
    (I : ObserverInterface World) :=
  Quotient (Setoid.ker I.observe)

/--
The canonical quotient projection sends an underlying state to its
observational-equivalence class.
-/
def observableClass
    {World : Type u}
    (I : ObserverInterface World)
    (x : World) :
    ObservableQuotient I :=
  Quotient.mk'' x

/--
The observation map descends to a map from observational-equivalence
classes to accessible observations.
-/
def quotientObservation
    {World : Type u}
    (I : ObserverInterface World) :
    ObservableQuotient I → I.Obs :=
  Setoid.kerLift I.observe

/--
Observing the equivalence class of an underlying state gives the same
observation as observing the original state.
-/
@[simp]
theorem quotientObservation_observableClass
    {World : Type u}
    (I : ObserverInterface World)
    (x : World) :
    quotientObservation I (observableClass I x) = I.observe x := by
  change Setoid.kerLift I.observe (Quotient.mk'' x) = I.observe x
  exact Setoid.kerLift_mk I.observe x

/--
Two canonical quotient states are equal exactly when their underlying
states are observationally equivalent.
-/
theorem observableClass_eq_iff_obsEq
    {World : Type u}
    (I : ObserverInterface World)
    (x y : World) :
    observableClass I x = observableClass I y ↔ ObsEq I x y := by
  constructor
  · intro hClass
    have hObserved :
        quotientObservation I (observableClass I x) =
          quotientObservation I (observableClass I y) :=
      congrArg (quotientObservation I) hClass
    change I.observe x = I.observe y
    calc
      I.observe x =
          quotientObservation I (observableClass I x) :=
        (quotientObservation_observableClass I x).symm
      _ = quotientObservation I (observableClass I y) := hObserved
      _ = I.observe y :=
        quotientObservation_observableClass I y
  · intro hObs
    apply Quotient.sound
    exact hObs

/--
The induced observation map from the observable quotient is
injective.

After observationally equivalent states have been identified, no
additional distinctions are lost by the induced map.
-/
theorem quotientObservation_injective
    {World : Type u}
    (I : ObserverInterface World) :
    Function.Injective (quotientObservation I) := by
  change Function.Injective (Setoid.kerLift I.observe)
  exact Setoid.kerLift_injective I.observe

/--
The observable quotient is equivalent to the range of observations
that the interface can actually produce.

The codomain may contain formally possible observations that are not
reachable from any underlying state. The quotient corresponds only
to the reachable range.
-/
noncomputable def observableQuotientEquivRange
    {World : Type u}
    (I : ObserverInterface World) :
    ObservableQuotient I ≃ Set.range I.observe :=
  Setoid.quotientKerEquivRange I.observe

/--
If every formally available observation is produced by some
underlying state, then the observable quotient is equivalent to the
entire observation space.
-/
noncomputable def observableQuotientEquivObs
    {World : Type u}
    (I : ObserverInterface World)
    (hSurjective : Function.Surjective I.observe) :
    ObservableQuotient I ≃ I.Obs :=
  Setoid.quotientKerEquivOfSurjective I.observe hSurjective

/-!
## Accessible quantities on the observable quotient
-/

/--
Every interface-accessible quantity descends to a well-defined
quantity on the observable quotient.
-/
def liftAccessibleQuantity
    {World : Type u}
    (I : ObserverInterface World)
    {Value : Type w}
    (q : World → Value)
    (hq : FactorsThrough I q) :
    ObservableQuotient I → Value :=
  Quotient.lift q (by
    intro x y hxy
    exact factorized_quantity_respects_obsEq I q hq hxy)

/--
Evaluating the lifted quantity on the equivalence class of a state
returns the quantity evaluated on the original state.
-/
@[simp]
theorem liftAccessibleQuantity_observableClass
    {World : Type u}
    (I : ObserverInterface World)
    {Value : Type w}
    (q : World → Value)
    (hq : FactorsThrough I q)
    (x : World) :
    liftAccessibleQuantity I q hq (observableClass I x) = q x := by
  rfl

/--
An interface-accessible quantity cannot distinguish two equal states
of the observable quotient.
-/
theorem lifted_quantity_respects_quotient_equality
    {World : Type u}
    (I : ObserverInterface World)
    {Value : Type w}
    (q : World → Value)
    (hq : FactorsThrough I q)
    {a b : ObservableQuotient I}
    (hab : a = b) :
    liftAccessibleQuantity I q hq a =
      liftAccessibleQuantity I q hq b := by
  exact congrArg (liftAccessibleQuantity I q hq) hab

/-!
## Universal property of the observable quotient

A quantity is compatible with the observer interface when it assigns
the same value to all observationally equivalent underlying states.

Every compatible quantity descends uniquely to the observable
quotient. Conversely, every quantity defined on the observable
quotient determines a compatible quantity on the underlying world.
-/

/--
A quantity respects observational equivalence when it assigns equal
values to underlying states that produce the same observation.
-/
def RespectsObsEq
    {World : Type u}
    (I : ObserverInterface World)
    {Value : Type w}
    (q : World → Value) : Prop :=
  ∀ x y : World, ObsEq I x y → q x = q y

/--
Every quantity that factors through the observer interface respects
observational equivalence.
-/
theorem factorsThrough_respects_obsEq
    {World : Type u}
    (I : ObserverInterface World)
    {Value : Type w}
    (q : World → Value)
    (hq : FactorsThrough I q) :
    RespectsObsEq I q := by
  intro x y hxy
  exact factorized_quantity_respects_obsEq I q hq hxy

/--
A quantity that respects observational equivalence descends to a
well-defined function on the observable quotient.
-/
def descendToObservableQuotient
    {World : Type u}
    (I : ObserverInterface World)
    {Value : Type w}
    (q : World → Value)
    (hq : RespectsObsEq I q) :
    ObservableQuotient I → Value :=
  Quotient.lift q (by
    intro x y hxy
    exact hq x y hxy)

/--
Evaluating the descended quantity on the class of an underlying state
returns the original quantity evaluated at that state.
-/
@[simp]
theorem descendToObservableQuotient_observableClass
    {World : Type u}
    (I : ObserverInterface World)
    {Value : Type w}
    (q : World → Value)
    (hq : RespectsObsEq I q)
    (x : World) :
    descendToObservableQuotient I q hq (observableClass I x) =
      q x := by
  rfl

/--
Every state of the observable quotient is represented by at least one
underlying world state.
-/
theorem observableClass_surjective
    {World : Type u}
    (I : ObserverInterface World) :
    Function.Surjective (observableClass I) := by
  intro a
  rcases Quotient.mk''_surjective a with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  change Quotient.mk'' x = a
  exact hx

/--
A function on the observable quotient is uniquely determined by its
values on canonical observational classes.
-/
theorem descendToObservableQuotient_unique
    {World : Type u}
    (I : ObserverInterface World)
    {Value : Type w}
    (q : World → Value)
    (hq : RespectsObsEq I q)
    (g : ObservableQuotient I → Value)
    (hg : ∀ x : World, g (observableClass I x) = q x) :
    g = descendToObservableQuotient I q hq := by
  funext a
  rcases observableClass_surjective I a with ⟨x, rfl⟩
  calc
    g (observableClass I x) = q x := hg x
    _ =
        descendToObservableQuotient I q hq
          (observableClass I x) :=
      (descendToObservableQuotient_observableClass
        I q hq x).symm

/--
A quantity factors through the observable quotient when it can be
computed entirely from an observational-equivalence class.
-/
def FactorsThroughObservableQuotient
    {World : Type u}
    (I : ObserverInterface World)
    {Value : Type w}
    (q : World → Value) : Prop :=
  ∃ qbar : ObservableQuotient I → Value,
    q = qbar ∘ observableClass I

/--
A quantity respects observational equivalence exactly when it factors
through the observable quotient.
-/
theorem respectsObsEq_iff_factorsThroughObservableQuotient
    {World : Type u}
    (I : ObserverInterface World)
    {Value : Type w}
    (q : World → Value) :
    RespectsObsEq I q ↔
      FactorsThroughObservableQuotient I q := by
  constructor
  · intro hRespect
    refine
      ⟨descendToObservableQuotient I q hRespect, ?_⟩
    funext x
    change
      q x =
        descendToObservableQuotient I q hRespect
          (observableClass I x)
    exact
      (descendToObservableQuotient_observableClass
        I q hRespect x).symm
  · rintro ⟨qbar, hFactor⟩
    intro x y hxy
    have hClass :
        observableClass I x = observableClass I y :=
      (observableClass_eq_iff_obsEq I x y).2 hxy
    have hx :
        q x = (qbar ∘ observableClass I) x :=
      congrArg (fun f => f x) hFactor
    have hy :
        q y = (qbar ∘ observableClass I) y :=
      congrArg (fun f => f y) hFactor
    calc
      q x = (qbar ∘ observableClass I) x := hx
      _ = qbar (observableClass I x) := rfl
      _ = qbar (observableClass I y) :=
        congrArg qbar hClass
      _ = (qbar ∘ observableClass I) y := rfl
      _ = q y := hy.symm

/--
Every quantity that factors through the original observation map also
factors through the observable quotient.
-/
theorem factorsThrough_implies_quotient_factorization
    {World : Type u}
    (I : ObserverInterface World)
    {Value : Type w}
    (q : World → Value)
    (hq : FactorsThrough I q) :
    FactorsThroughObservableQuotient I q := by
  apply
    (respectsObsEq_iff_factorsThroughObservableQuotient
      I q).1
  exact factorsThrough_respects_obsEq I q hq

/--
Every quantity compatible with observational equivalence possesses a
unique representation on the observable quotient.
-/
theorem observableQuotient_universal_property
    {World : Type u}
    (I : ObserverInterface World)
    {Value : Type w}
    (q : World → Value)
    (hq : RespectsObsEq I q) :
    ∃! qbar : ObservableQuotient I → Value,
      q = qbar ∘ observableClass I := by
  refine
    ⟨descendToObservableQuotient I q hq, ?_, ?_⟩
  · funext x
    change
      q x =
        descendToObservableQuotient I q hq
          (observableClass I x)
    exact
      (descendToObservableQuotient_observableClass
        I q hq x).symm
  · intro g hg
    apply descendToObservableQuotient_unique I q hq g
    intro x
    have hx :
        q x = g (observableClass I x) :=
      congrArg (fun f => f x) hg
    exact hx.symm

/--
A quantity that takes different values on two observationally
equivalent states cannot factor through the observer interface.
-/
theorem observable_variation_prevents_factorization
    {World : Type u}
    (I : ObserverInterface World)
    {Value : Type w}
    (q : World → Value)
    {x y : World}
    (hxy : ObsEq I x y)
    (hDifferent : q x ≠ q y) :
    ¬ FactorsThrough I q := by
  intro hFactor
  apply hDifferent
  exact
    factorized_quantity_respects_obsEq
      I q hFactor hxy

/--
A quantity that takes different values on two observationally
equivalent states cannot be represented on the observable quotient.
-/
theorem observable_variation_prevents_quotient_factorization
    {World : Type u}
    (I : ObserverInterface World)
    {Value : Type w}
    (q : World → Value)
    {x y : World}
    (hxy : ObsEq I x y)
    (hDifferent : q x ≠ q y) :
    ¬ FactorsThroughObservableQuotient I q := by
  intro hFactor
  have hRespect : RespectsObsEq I q :=
    (respectsObsEq_iff_factorsThroughObservableQuotient
      I q).2 hFactor
  exact hDifferent (hRespect x y hxy)

/-!
## Interface refinement and information ordering

An interface is finer than another interface when every observation
available to the coarser interface can be computed from the finer
observation.

A finer interface may preserve distinctions that the coarser
interface removes. The induced map between observable quotients
therefore runs from the finer quotient onto the coarser quotient.
-/

/--
`Fine` refines `Coarse` when there is a map from fine observations to
coarse observations that reproduces the coarse observation of every
underlying state.
-/
def InterfaceRefines
    {World : Type u}
    (Fine Coarse : ObserverInterface World) : Prop :=
  ∃ coarsen : Fine.Obs → Coarse.Obs,
    ∀ x : World,
      Coarse.observe x = coarsen (Fine.observe x)

/--
Every observer interface refines itself.
-/
theorem interfaceRefines_refl
    {World : Type u}
    (I : ObserverInterface World) :
    InterfaceRefines I I := by
  refine ⟨id, ?_⟩
  intro x
  rfl

/--
Interface refinement is transitive.
-/
theorem interfaceRefines_trans
    {World : Type u}
    (Fine Middle Coarse : ObserverInterface World)
    (hFineMiddle : InterfaceRefines Fine Middle)
    (hMiddleCoarse : InterfaceRefines Middle Coarse) :
    InterfaceRefines Fine Coarse := by
  rcases hFineMiddle with
    ⟨fineToMiddle, hFineToMiddle⟩
  rcases hMiddleCoarse with
    ⟨middleToCoarse, hMiddleToCoarse⟩
  refine ⟨middleToCoarse ∘ fineToMiddle, ?_⟩
  intro x
  calc
    Coarse.observe x =
        middleToCoarse (Middle.observe x) :=
      hMiddleToCoarse x
    _ =
        middleToCoarse
          (fineToMiddle (Fine.observe x)) :=
      congrArg middleToCoarse (hFineToMiddle x)
    _ =
        (middleToCoarse ∘ fineToMiddle)
          (Fine.observe x) := rfl

/--
States that are indistinguishable to a finer interface are also
indistinguishable to every interface obtained by coarsening it.
-/
theorem refinement_preserves_obsEq
    {World : Type u}
    (Fine Coarse : ObserverInterface World)
    (hRefines : InterfaceRefines Fine Coarse)
    {x y : World}
    (hxy : ObsEq Fine x y) :
    ObsEq Coarse x y := by
  rcases hRefines with ⟨coarsen, hCoarsen⟩
  change Fine.observe x = Fine.observe y at hxy
  change Coarse.observe x = Coarse.observe y
  calc
    Coarse.observe x =
        coarsen (Fine.observe x) :=
      hCoarsen x
    _ = coarsen (Fine.observe y) :=
      congrArg coarsen hxy
    _ = Coarse.observe y :=
      (hCoarsen y).symm

/--
Every quantity available through a coarser interface is also
available through a finer interface.
-/
theorem factorization_monotone_under_refinement
    {World : Type u}
    (Fine Coarse : ObserverInterface World)
    (hRefines : InterfaceRefines Fine Coarse)
    {Value : Type w}
    (q : World → Value)
    (hq : FactorsThrough Coarse q) :
    FactorsThrough Fine q := by
  rcases hRefines with ⟨coarsen, hCoarsen⟩
  rcases hq with ⟨qbar, hFactor⟩
  refine ⟨qbar ∘ coarsen, ?_⟩
  funext x
  have hAtX :
      q x = qbar (Coarse.observe x) := by
    have hPoint := congrFun hFactor x
    change q x = qbar (Coarse.observe x) at hPoint
    exact hPoint
  calc
    q x = qbar (Coarse.observe x) := hAtX
    _ = qbar (coarsen (Fine.observe x)) :=
      congrArg qbar (hCoarsen x)
    _ =
        (qbar ∘ coarsen) (Fine.observe x) := rfl

/--
Every test available to a coarser interface can be simulated by a
test receiving the finer observation.
-/
theorem coarse_test_simulated_by_fine
    {World : Type u}
    (Fine Coarse : ObserverInterface World)
    (hRefines : InterfaceRefines Fine Coarse)
    (test : InternalTest Coarse) :
    ∃ fineTest : InternalTest Fine,
      ∀ x : World,
        fineTest (Fine.observe x) =
          test (Coarse.observe x) := by
  rcases hRefines with ⟨coarsen, hCoarsen⟩
  refine ⟨fun o => test (coarsen o), ?_⟩
  intro x
  exact congrArg test (hCoarsen x).symm

/--
If exact reconstruction is possible from a coarser observation, then
it is also possible from the finer observation.
-/
theorem coarse_exact_decoder_implies_fine_exact_decoder
    {World : Type u}
    (Fine Coarse : ObserverInterface World)
    (hRefines : InterfaceRefines Fine Coarse)
    (hDecoder : HasExactDecoder Coarse) :
    HasExactDecoder Fine := by
  rcases hRefines with ⟨coarsen, hCoarsen⟩
  rcases hDecoder with ⟨decode, hLeft⟩
  refine ⟨decode ∘ coarsen, ?_⟩
  intro x
  change decode (coarsen (Fine.observe x)) = x
  calc
    decode (coarsen (Fine.observe x)) =
        decode (Coarse.observe x) :=
      congrArg decode (hCoarsen x).symm
    _ = x := hLeft x

/--
If the coarser observation map is injective, then the finer
observation map must also be injective.
-/
theorem coarse_injective_implies_fine_injective
    {World : Type u}
    (Fine Coarse : ObserverInterface World)
    (hRefines : InterfaceRefines Fine Coarse)
    (hCoarseInjective :
      Function.Injective Coarse.observe) :
    Function.Injective Fine.observe := by
  intro x y hFine
  apply hCoarseInjective
  change ObsEq Fine x y at hFine
  exact
    refinement_preserves_obsEq
      Fine Coarse hRefines hFine

/--
If the finer observation map is not injective, then no coarsening of
that interface can be injective.
-/
theorem fine_noninjective_implies_coarse_noninjective
    {World : Type u}
    (Fine Coarse : ObserverInterface World)
    (hRefines : InterfaceRefines Fine Coarse)
    (hFineNotInjective :
      ¬ Function.Injective Fine.observe) :
    ¬ Function.Injective Coarse.observe := by
  intro hCoarseInjective
  apply hFineNotInjective
  exact
    coarse_injective_implies_fine_injective
      Fine Coarse hRefines hCoarseInjective

/-!
## Refinement maps between observable quotients
-/

/--
A refinement induces a canonical map from the finer observable
quotient to the coarser observable quotient.
-/
def quotientMapOfRefinement
    {World : Type u}
    (Fine Coarse : ObserverInterface World)
    (hRefines : InterfaceRefines Fine Coarse) :
    ObservableQuotient Fine →
      ObservableQuotient Coarse :=
  Quotient.lift
    (fun x => observableClass Coarse x)
    (by
      intro x y hxy
      apply
        (observableClass_eq_iff_obsEq
          Coarse x y).2
      change ObsEq Fine x y at hxy
      exact
        refinement_preserves_obsEq
          Fine Coarse hRefines hxy)

/--
The refinement map sends the fine observational class of a state to
its coarse observational class.
-/
@[simp]
theorem quotientMapOfRefinement_observableClass
    {World : Type u}
    (Fine Coarse : ObserverInterface World)
    (hRefines : InterfaceRefines Fine Coarse)
    (x : World) :
    quotientMapOfRefinement
        Fine Coarse hRefines
        (observableClass Fine x) =
      observableClass Coarse x := by
  rfl

/--
The refinement map between observable quotients is surjective.

Every coarse observational class is the image of at least one fine
observational class.
-/
theorem quotientMapOfRefinement_surjective
    {World : Type u}
    (Fine Coarse : ObserverInterface World)
    (hRefines : InterfaceRefines Fine Coarse) :
    Function.Surjective
      (quotientMapOfRefinement
        Fine Coarse hRefines) := by
  intro a
  rcases observableClass_surjective Coarse a with
    ⟨x, hx⟩
  refine ⟨observableClass Fine x, ?_⟩
  calc
    quotientMapOfRefinement
        Fine Coarse hRefines
        (observableClass Fine x) =
      observableClass Coarse x :=
        quotientMapOfRefinement_observableClass
          Fine Coarse hRefines x
    _ = a := hx

/--
When the coarse interface identifies two states that the fine
interface distinguishes, the induced quotient map is not injective.
-/
theorem quotientMap_not_injective_of_collapsed_pair
    {World : Type u}
    (Fine Coarse : ObserverInterface World)
    (hRefines : InterfaceRefines Fine Coarse)
    {x y : World}
    (hFineDistinguishes : ¬ ObsEq Fine x y)
    (hCoarseIdentifies : ObsEq Coarse x y) :
    ¬ Function.Injective
      (quotientMapOfRefinement
        Fine Coarse hRefines) := by
  intro hInjective
  apply hFineDistinguishes
  have hFineClass :
      observableClass Fine x =
        observableClass Fine y := by
    apply hInjective
    calc
      quotientMapOfRefinement
          Fine Coarse hRefines
          (observableClass Fine x) =
        observableClass Coarse x :=
          quotientMapOfRefinement_observableClass
            Fine Coarse hRefines x
      _ = observableClass Coarse y :=
        (observableClass_eq_iff_obsEq
          Coarse x y).2 hCoarseIdentifies
      _ =
          quotientMapOfRefinement
            Fine Coarse hRefines
            (observableClass Fine y) :=
        (quotientMapOfRefinement_observableClass
          Fine Coarse hRefines y).symm
  exact
    (observableClass_eq_iff_obsEq
      Fine x y).1 hFineClass

/-!
## Equal observational resolution
-/

/--
Two interfaces have the same observational resolution when they
identify exactly the same pairs of underlying states.
-/
def SameObservationalResolution
    {World : Type u}
    (I J : ObserverInterface World) : Prop :=
  ∀ x y : World,
    ObsEq I x y ↔ ObsEq J x y

/--
Every interface has the same observational resolution as itself.
-/
theorem sameObservationalResolution_refl
    {World : Type u}
    (I : ObserverInterface World) :
    SameObservationalResolution I I := by
  intro x y
  rfl

/--
Equal observational resolution is symmetric.
-/
theorem sameObservationalResolution_symm
    {World : Type u}
    {I J : ObserverInterface World}
    (hIJ : SameObservationalResolution I J) :
    SameObservationalResolution J I := by
  intro x y
  exact (hIJ x y).symm

/--
Equal observational resolution is transitive.
-/
theorem sameObservationalResolution_trans
    {World : Type u}
    {I J K : ObserverInterface World}
    (hIJ : SameObservationalResolution I J)
    (hJK : SameObservationalResolution J K) :
    SameObservationalResolution I K := by
  intro x y
  exact (hIJ x y).trans (hJK x y)

/--
Mutually refining interfaces have the same observational resolution.
-/
theorem mutual_refinement_same_resolution
    {World : Type u}
    (I J : ObserverInterface World)
    (hIJ : InterfaceRefines I J)
    (hJI : InterfaceRefines J I) :
    SameObservationalResolution I J := by
  intro x y
  constructor
  · intro hI
    exact refinement_preserves_obsEq I J hIJ hI
  · intro hJ
    exact refinement_preserves_obsEq J I hJI hJ

/--
Under mutual refinement, the induced quotient map is injective.
-/
theorem quotientMapOfMutualRefinement_injective
    {World : Type u}
    (I J : ObserverInterface World)
    (hIJ : InterfaceRefines I J)
    (hJI : InterfaceRefines J I) :
    Function.Injective
      (quotientMapOfRefinement I J hIJ) := by
  intro a b hab
  rcases observableClass_surjective I a with
    ⟨x, rfl⟩
  rcases observableClass_surjective I b with
    ⟨y, rfl⟩
  apply (observableClass_eq_iff_obsEq I x y).2
  apply refinement_preserves_obsEq J I hJI
  apply (observableClass_eq_iff_obsEq J x y).1
  calc
    observableClass J x =
        quotientMapOfRefinement
          I J hIJ
          (observableClass I x) :=
      (quotientMapOfRefinement_observableClass
        I J hIJ x).symm
    _ =
        quotientMapOfRefinement
          I J hIJ
          (observableClass I y) :=
      hab
    _ = observableClass J y :=
      quotientMapOfRefinement_observableClass
        I J hIJ y

/--
Under mutual refinement, the induced quotient map is bijective.
-/
theorem quotientMapOfMutualRefinement_bijective
    {World : Type u}
    (I J : ObserverInterface World)
    (hIJ : InterfaceRefines I J)
    (hJI : InterfaceRefines J I) :
    Function.Bijective
      (quotientMapOfRefinement I J hIJ) := by
  constructor
  · exact
      quotientMapOfMutualRefinement_injective
        I J hIJ hJI
  · exact
      quotientMapOfRefinement_surjective
        I J hIJ

/-!
## Strict refinement and irreversible observational loss

A strict refinement preserves every distinction available to a
coarser interface while also preserving at least one distinction that
the coarser interface removes.

Strict refinement therefore describes genuine loss of observational
resolution rather than a mere change of representation.
-/

/--
`Fine` strictly refines `Coarse` when `Fine` refines `Coarse` and
there is at least one pair of states distinguished by `Fine` but
identified by `Coarse`.
-/
def StrictlyRefines
    {World : Type u}
    (Fine Coarse : ObserverInterface World) : Prop :=
  InterfaceRefines Fine Coarse ∧
    ∃ x y : World,
      ¬ ObsEq Fine x y ∧ ObsEq Coarse x y

/--
Every strict refinement is an interface refinement.
-/
theorem strictlyRefines_refines
    {World : Type u}
    {Fine Coarse : ObserverInterface World}
    (hStrict : StrictlyRefines Fine Coarse) :
    InterfaceRefines Fine Coarse := by
  exact hStrict.1

/--
A strict refinement contains a pair of states that the finer
interface distinguishes and the coarser interface identifies.
-/
theorem strictlyRefines_has_collapsed_pair
    {World : Type u}
    {Fine Coarse : ObserverInterface World}
    (hStrict : StrictlyRefines Fine Coarse) :
    ∃ x y : World,
      ¬ ObsEq Fine x y ∧ ObsEq Coarse x y := by
  exact hStrict.2

/--
No interface strictly refines itself.
-/
theorem strictlyRefines_irrefl
    {World : Type u}
    (I : ObserverInterface World) :
    ¬ StrictlyRefines I I := by
  intro hStrict
  rcases hStrict.2 with
    ⟨x, y, hDistinguished, hIdentified⟩
  exact hDistinguished hIdentified

/--
A strict refinement cannot be reversed by another refinement.

If `Fine` strictly refines `Coarse`, then `Coarse` cannot refine
`Fine`.
-/
theorem strictlyRefines_prevents_reverse_refinement
    {World : Type u}
    (Fine Coarse : ObserverInterface World)
    (hStrict : StrictlyRefines Fine Coarse) :
    ¬ InterfaceRefines Coarse Fine := by
  intro hReverse
  rcases hStrict.2 with
    ⟨x, y, hFineDistinguishes, hCoarseIdentifies⟩
  apply hFineDistinguishes
  exact
    refinement_preserves_obsEq
      Coarse Fine hReverse hCoarseIdentifies

/--
Strictly ordered interfaces cannot have the same observational
resolution.
-/
theorem strictlyRefines_not_same_resolution
    {World : Type u}
    (Fine Coarse : ObserverInterface World)
    (hStrict : StrictlyRefines Fine Coarse) :
    ¬ SameObservationalResolution Fine Coarse := by
  intro hSame
  rcases hStrict.2 with
    ⟨x, y, hFineDistinguishes, hCoarseIdentifies⟩
  apply hFineDistinguishes
  exact (hSame x y).mpr hCoarseIdentifies

/--
Strict refinement implies that the coarser observation map is not
injective.
-/
theorem strictlyRefines_coarse_not_injective
    {World : Type u}
    (Fine Coarse : ObserverInterface World)
    (hStrict : StrictlyRefines Fine Coarse) :
    ¬ Function.Injective Coarse.observe := by
  rcases hStrict.2 with
    ⟨x, y, hFineDistinguishes, hCoarseIdentifies⟩
  intro hInjective
  have hxy : x = y :=
    hInjective hCoarseIdentifies
  subst y
  exact hFineDistinguishes (obsEq_refl Fine x)

/--
A strictly coarser interface cannot possess a globally exact decoder.
-/
theorem strictlyRefines_coarse_has_no_exact_decoder
    {World : Type u}
    (Fine Coarse : ObserverInterface World)
    (hStrict : StrictlyRefines Fine Coarse) :
    ¬ HasExactDecoder Coarse := by
  exact
    no_exact_decoder_of_not_injective
      Coarse
      (strictlyRefines_coarse_not_injective
        Fine Coarse hStrict)

/--
The quotient map produced by strict refinement is not injective.
-/
theorem strictlyRefines_quotientMap_not_injective
    {World : Type u}
    (Fine Coarse : ObserverInterface World)
    (hStrict : StrictlyRefines Fine Coarse) :
    ¬ Function.Injective
      (quotientMapOfRefinement
        Fine Coarse hStrict.1) := by
  rcases hStrict.2 with
    ⟨x, y, hFineDistinguishes, hCoarseIdentifies⟩
  exact
    quotientMap_not_injective_of_collapsed_pair
      Fine
      Coarse
      hStrict.1
      hFineDistinguishes
      hCoarseIdentifies

/--
The quotient map produced by strict refinement is not bijective.
-/
theorem strictlyRefines_quotientMap_not_bijective
    {World : Type u}
    (Fine Coarse : ObserverInterface World)
    (hStrict : StrictlyRefines Fine Coarse) :
    ¬ Function.Bijective
      (quotientMapOfRefinement
        Fine Coarse hStrict.1) := by
  intro hBijective
  exact
    (strictlyRefines_quotientMap_not_injective
      Fine Coarse hStrict)
      hBijective.1

/-!
## Composition of strict and non-strict refinements
-/

/--
A strict refinement followed by an ordinary refinement remains
strict.
-/
theorem strictlyRefines_of_strict_then_refines
    {World : Type u}
    (Fine Middle Coarse : ObserverInterface World)
    (hFineMiddle : StrictlyRefines Fine Middle)
    (hMiddleCoarse : InterfaceRefines Middle Coarse) :
    StrictlyRefines Fine Coarse := by
  refine
    ⟨interfaceRefines_trans
      Fine Middle Coarse
      hFineMiddle.1
      hMiddleCoarse, ?_⟩
  rcases hFineMiddle.2 with
    ⟨x, y, hFineDistinguishes, hMiddleIdentifies⟩
  refine
    ⟨x, y, hFineDistinguishes, ?_⟩
  exact
    refinement_preserves_obsEq
      Middle Coarse
      hMiddleCoarse
      hMiddleIdentifies

/--
An ordinary refinement followed by a strict refinement remains
strict.
-/
theorem strictlyRefines_of_refines_then_strict
    {World : Type u}
    (Fine Middle Coarse : ObserverInterface World)
    (hFineMiddle : InterfaceRefines Fine Middle)
    (hMiddleCoarse : StrictlyRefines Middle Coarse) :
    StrictlyRefines Fine Coarse := by
  refine
    ⟨interfaceRefines_trans
      Fine Middle Coarse
      hFineMiddle
      hMiddleCoarse.1, ?_⟩
  rcases hMiddleCoarse.2 with
    ⟨x, y, hMiddleDistinguishes, hCoarseIdentifies⟩
  refine
    ⟨x, y, ?_, hCoarseIdentifies⟩
  intro hFineIdentifies
  apply hMiddleDistinguishes
  exact
    refinement_preserves_obsEq
      Fine Middle
      hFineMiddle
      hFineIdentifies

/--
Strict refinement is transitive.
-/
theorem strictlyRefines_trans
    {World : Type u}
    (Fine Middle Coarse : ObserverInterface World)
    (hFineMiddle : StrictlyRefines Fine Middle)
    (hMiddleCoarse : StrictlyRefines Middle Coarse) :
    StrictlyRefines Fine Coarse := by
  exact
    strictlyRefines_of_refines_then_strict
      Fine
      Middle
      Coarse
      hFineMiddle.1
      hMiddleCoarse

/--
Strict refinement is asymmetric.
-/
theorem strictlyRefines_asymm
    {World : Type u}
    {Fine Coarse : ObserverInterface World}
    (hStrict : StrictlyRefines Fine Coarse) :
    ¬ StrictlyRefines Coarse Fine := by
  intro hReverseStrict
  exact
    strictlyRefines_prevents_reverse_refinement
      Fine Coarse hStrict hReverseStrict.1

/-!
## Equivalent quotient representations

Mutually refining interfaces may use different observation types, but
their observable quotient spaces contain the same distinctions.
-/

/--
Mutual refinement determines an equivalence between the two
observable quotient spaces.
-/
noncomputable def observableQuotientEquivOfMutualRefinement
    {World : Type u}
    (I J : ObserverInterface World)
    (hIJ : InterfaceRefines I J)
    (hJI : InterfaceRefines J I) :
    ObservableQuotient I ≃ ObservableQuotient J :=
  Equiv.ofBijective
    (quotientMapOfRefinement I J hIJ)
    (quotientMapOfMutualRefinement_bijective
      I J hIJ hJI)

/--
The quotient equivalence sends the observational class of each
underlying state to its class under the mutually refining interface.
-/
@[simp]
theorem observableQuotientEquivOfMutualRefinement_observableClass
    {World : Type u}
    (I J : ObserverInterface World)
    (hIJ : InterfaceRefines I J)
    (hJI : InterfaceRefines J I)
    (x : World) :
    observableQuotientEquivOfMutualRefinement
        I J hIJ hJI
        (observableClass I x) =
      observableClass J x := by
  change
    quotientMapOfRefinement
        I J hIJ
        (observableClass I x) =
      observableClass J x
  exact
    quotientMapOfRefinement_observableClass
      I J hIJ x

/-!
## Latent multiplicity and empirical underdetermination

Observational equivalence determines which outcomes can be accessed
through an interface, but it does not uniquely determine the latent
structure that generates those outcomes.

A model can be expanded by duplicating every latent state while
preserving exactly the same accessible observations. No admissible
experiment can distinguish the original model from this duplicated
model through its possible outcomes.
-/

/--
The outcome set of an experiment contains every result that the
experiment can produce under a given generative model.
-/
def ExperimentOutcomeSet
    {Obs : Type u₂}
    {Result : Type u₃}
    (M : GenerativeModel Obs)
    (experiment : AdmissibleExperiment Obs Result) :
    Set Result :=
  {result | ExperimentCanProduce M experiment result}

/--
Observationally equivalent models have equal outcome sets under every
admissible experiment.
-/
theorem modelObsEq_preserves_experimentOutcomeSet
    {Obs : Type u₂}
    {Result : Type u₃}
    (M N : GenerativeModel Obs)
    (hMN : ModelObsEq M N)
    (experiment : AdmissibleExperiment Obs Result) :
    ExperimentOutcomeSet M experiment =
      ExperimentOutcomeSet N experiment := by
  ext result
  change
    ExperimentCanProduce M experiment result ↔
      ExperimentCanProduce N experiment result
  exact
    modelObsEq_preserves_experiment_results
      M N hMN experiment result

/--
An experiment separates two models when their possible outcome sets
are different.
-/
def ExperimentSeparates
    {Obs : Type u₂}
    {Result : Type u₃}
    (M N : GenerativeModel Obs)
    (experiment : AdmissibleExperiment Obs Result) : Prop :=
  ExperimentOutcomeSet M experiment ≠
    ExperimentOutcomeSet N experiment

/--
No admissible experiment separates observationally equivalent models.
-/
theorem modelObsEq_prevents_experimental_separation
    {Obs : Type u₂}
    {Result : Type u₃}
    (M N : GenerativeModel Obs)
    (hMN : ModelObsEq M N)
    (experiment : AdmissibleExperiment Obs Result) :
    ¬ ExperimentSeparates M N experiment := by
  intro hSeparates
  apply hSeparates
  exact
    modelObsEq_preserves_experimentOutcomeSet
      M N hMN experiment

/-!
## Duplicating latent structure without changing observations
-/

/--
The duplicated model replaces every latent state `x` with two latent
states, `(x, false)` and `(x, true)`, while ignoring the Boolean
coordinate during observation.
-/
def duplicateModel
    {Obs : Type u₂}
    (M : GenerativeModel Obs) :
    GenerativeModel Obs where
  Latent := M.Latent × Bool
  observe state := M.observe state.1

/--
Every observation produced by the original model is produced by the
duplicated model, and every observation produced by the duplicated
model is produced by the original model.
-/
theorem modelObsEq_duplicateModel
    {Obs : Type u₂}
    (M : GenerativeModel Obs) :
    ModelObsEq M (duplicateModel M) := by
  intro observation
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨(x, false), hx⟩
  · rintro ⟨state, hState⟩
    exact ⟨state.1, hState⟩

/--
The original model and its duplicated version have equal possible
outcome sets under every admissible experiment.
-/
theorem duplicateModel_preserves_experimentOutcomeSet
    {Obs : Type u₂}
    {Result : Type u₃}
    (M : GenerativeModel Obs)
    (experiment : AdmissibleExperiment Obs Result) :
    ExperimentOutcomeSet M experiment =
      ExperimentOutcomeSet (duplicateModel M) experiment := by
  exact
    modelObsEq_preserves_experimentOutcomeSet
      M
      (duplicateModel M)
      (modelObsEq_duplicateModel M)
      experiment

/--
No admissible experiment separates a model from its duplicated latent
representation.
-/
theorem no_experiment_separates_duplicateModel
    {Obs : Type u₂}
    {Result : Type u₃}
    (M : GenerativeModel Obs)
    (experiment : AdmissibleExperiment Obs Result) :
    ¬ ExperimentSeparates M (duplicateModel M) experiment := by
  exact
    modelObsEq_prevents_experimental_separation
      M
      (duplicateModel M)
      (modelObsEq_duplicateModel M)
      experiment

/-!
## Exact latent reconstruction
-/

/--
A globally exact latent decoder reconstructs every latent state from
its accessible observation.
-/
def HasExactLatentDecoder
    {Obs : Type u₂}
    (M : GenerativeModel Obs) : Prop :=
  ∃ decode : Obs → M.Latent,
    Function.LeftInverse decode M.observe

/--
A globally exact latent decoder can exist only when the model's
observation map is injective.
-/
theorem exactLatentDecoder_implies_injective
    {Obs : Type u₂}
    (M : GenerativeModel Obs)
    (hDecoder : HasExactLatentDecoder M) :
    Function.Injective M.observe := by
  rcases hDecoder with ⟨decode, hLeft⟩
  exact Function.LeftInverse.injective hLeft

/--
When the original latent state space is inhabited, the duplicated
model contains two distinct latent states that produce the same
accessible observation.
-/
theorem duplicateModel_has_latent_collision
    {Obs : Type u₂}
    (M : GenerativeModel Obs)
    [Nonempty M.Latent] :
    ∃ a b : (duplicateModel M).Latent,
      a ≠ b ∧
        (duplicateModel M).observe a =
          (duplicateModel M).observe b := by
  classical
  let x : M.Latent :=
    Classical.choice (inferInstance : Nonempty M.Latent)
  refine ⟨(x, false), (x, true), ?_, rfl⟩
  intro hEqual
  have hBool : false = true :=
    congrArg Prod.snd hEqual
  cases hBool

/--
The duplicated model's observation map is not injective whenever the
original latent state space is inhabited.
-/
theorem duplicateModel_observe_not_injective
    {Obs : Type u₂}
    (M : GenerativeModel Obs)
    [Nonempty M.Latent] :
    ¬ Function.Injective (duplicateModel M).observe := by
  intro hInjective
  rcases duplicateModel_has_latent_collision M with
    ⟨a, b, hDistinct, hObservation⟩
  apply hDistinct
  exact hInjective hObservation

/--
The duplicated model cannot possess a globally exact latent decoder
whenever the original latent state space is inhabited.
-/
theorem duplicateModel_has_no_exactLatentDecoder
    {Obs : Type u₂}
    (M : GenerativeModel Obs)
    [Nonempty M.Latent] :
    ¬ HasExactLatentDecoder (duplicateModel M) := by
  intro hDecoder
  have hInjective :
      Function.Injective (duplicateModel M).observe :=
    exactLatentDecoder_implies_injective
      (duplicateModel M)
      hDecoder
  exact
    duplicateModel_observe_not_injective
      M
      hInjective

/--
Latent multiplicity is observationally underdetermined.

Every inhabited model has an observationally equivalent duplicated
model whose latent states cannot be reconstructed exactly from the
accessible observations.
-/
theorem latent_multiplicity_is_observationally_underdetermined
    {Obs : Type u₂}
    (M : GenerativeModel Obs)
    [Nonempty M.Latent] :
    ModelObsEq M (duplicateModel M) ∧
      ¬ HasExactLatentDecoder (duplicateModel M) := by
  constructor
  · exact modelObsEq_duplicateModel M
  · exact duplicateModel_has_no_exactLatentDecoder M

/--
The duplicated model simultaneously preserves every experimentally
accessible outcome and introduces an unrecoverable latent distinction.
-/
theorem duplicated_latent_distinction_is_empirically_hidden
    {Obs : Type u₂}
    {Result : Type u₃}
    (M : GenerativeModel Obs)
    [Nonempty M.Latent]
    (experiment : AdmissibleExperiment Obs Result) :
    ExperimentOutcomeSet M experiment =
        ExperimentOutcomeSet (duplicateModel M) experiment ∧
      ¬ Function.Injective (duplicateModel M).observe := by
  constructor
  · exact
      duplicateModel_preserves_experimentOutcomeSet
        M experiment
  · exact duplicateModel_observe_not_injective M

/-!
## Latent covers and hidden-state extensions

A latent cover is a richer generative model equipped with a
surjective projection onto a base model.

The projection preserves observations. Therefore, every latent state
of the richer model corresponds to a latent state of the base model
with the same accessible observation.

A latent cover may contain distinctions that are absent from the base
model while remaining observationally equivalent to it.
-/

/--
`Extended` is a latent cover of `Base` when there is a surjective map
from extended latent states to base latent states that preserves
accessible observations.
-/
structure LatentCover
    {Obs : Type u₂}
    (Extended Base : GenerativeModel Obs) where
  project : Extended.Latent → Base.Latent
  project_surjective : Function.Surjective project
  observation_preserved :
    ∀ x : Extended.Latent,
      Extended.observe x = Base.observe (project x)

/--
Every model is a latent cover of itself.
-/
def latentCoverRefl
    {Obs : Type u₂}
    (M : GenerativeModel Obs) :
    LatentCover M M where
  project := id
  project_surjective := by
    intro x
    exact ⟨x, rfl⟩
  observation_preserved := by
    intro x
    rfl

/--
Latent covers compose.

If `Extended` covers `Middle` and `Middle` covers `Base`, then
`Extended` covers `Base`.
-/
def latentCoverComp
    {Obs : Type u₂}
    (Extended Middle Base : GenerativeModel Obs)
    (hExtendedMiddle : LatentCover Extended Middle)
    (hMiddleBase : LatentCover Middle Base) :
    LatentCover Extended Base where
  project :=
    hMiddleBase.project ∘ hExtendedMiddle.project
  project_surjective := by
    intro z
    rcases hMiddleBase.project_surjective z with
      ⟨y, hy⟩
    rcases hExtendedMiddle.project_surjective y with
      ⟨x, hx⟩
    refine ⟨x, ?_⟩
    change
      hMiddleBase.project
          (hExtendedMiddle.project x) =
        z
    calc
      hMiddleBase.project
          (hExtendedMiddle.project x) =
        hMiddleBase.project y :=
          congrArg hMiddleBase.project hx
      _ = z := hy
  observation_preserved := by
    intro x
    calc
      Extended.observe x =
          Middle.observe
            (hExtendedMiddle.project x) :=
        hExtendedMiddle.observation_preserved x
      _ =
          Base.observe
            (hMiddleBase.project
              (hExtendedMiddle.project x)) :=
        hMiddleBase.observation_preserved
          (hExtendedMiddle.project x)
      _ =
          Base.observe
            ((hMiddleBase.project ∘
                hExtendedMiddle.project) x) := rfl

/--
A latent cover and its base model are observationally equivalent.
-/
theorem modelObsEq_of_latentCover
    {Obs : Type u₂}
    (Extended Base : GenerativeModel Obs)
    (cover : LatentCover Extended Base) :
    ModelObsEq Extended Base := by
  intro observation
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨cover.project x, ?_⟩
    calc
      Base.observe (cover.project x) =
          Extended.observe x :=
        (cover.observation_preserved x).symm
      _ = observation := hx
  · rintro ⟨y, hy⟩
    rcases cover.project_surjective y with
      ⟨x, hx⟩
    refine ⟨x, ?_⟩
    calc
      Extended.observe x =
          Base.observe (cover.project x) :=
        cover.observation_preserved x
      _ = Base.observe y :=
        congrArg Base.observe hx
      _ = observation := hy

/--
A latent cover preserves the possible result set of every admissible
experiment.
-/
theorem latentCover_preserves_experimentOutcomeSet
    {Obs : Type u₂}
    {Result : Type u₃}
    (Extended Base : GenerativeModel Obs)
    (cover : LatentCover Extended Base)
    (experiment : AdmissibleExperiment Obs Result) :
    ExperimentOutcomeSet Extended experiment =
      ExperimentOutcomeSet Base experiment := by
  exact
    modelObsEq_preserves_experimentOutcomeSet
      Extended
      Base
      (modelObsEq_of_latentCover
        Extended Base cover)
      experiment

/--
No admissible experiment separates a latent cover from its base
model.
-/
theorem latentCover_prevents_experimental_separation
    {Obs : Type u₂}
    {Result : Type u₃}
    (Extended Base : GenerativeModel Obs)
    (cover : LatentCover Extended Base)
    (experiment : AdmissibleExperiment Obs Result) :
    ¬ ExperimentSeparates Extended Base experiment := by
  exact
    modelObsEq_prevents_experimental_separation
      Extended
      Base
      (modelObsEq_of_latentCover
        Extended Base cover)
      experiment

/-!
## Hidden-factor extensions

A hidden-factor extension attaches an additional coordinate to every
latent state while leaving the observation map independent of that
coordinate.

The added coordinate may contain arbitrarily many distinctions, but
none of them are visible through the original observation map.
-/

/--
The hidden-factor extension of a model attaches a hidden coordinate
to every latent state and ignores that coordinate during observation.
-/
def hiddenExtensionModel
    {Obs : Type u₂}
    (M : GenerativeModel Obs)
    (Hidden : Type u₁) :
    GenerativeModel Obs where
  Latent := M.Latent × Hidden
  observe state := M.observe state.1

/--
Choosing one hidden value produces a surjective projection from the
hidden extension onto the original model.
-/
def hiddenExtensionCover
    {Obs : Type u₂}
    (M : GenerativeModel Obs)
    (Hidden : Type u₁)
    (anchor : Hidden) :
    LatentCover (hiddenExtensionModel M Hidden) M where
  project := Prod.fst
  project_surjective := by
    intro x
    exact ⟨(x, anchor), rfl⟩
  observation_preserved := by
    intro state
    rfl

/--
Every inhabited hidden-factor extension is observationally equivalent
to the original model.
-/
theorem modelObsEq_hiddenExtensionModel
    {Obs : Type u₂}
    (M : GenerativeModel Obs)
    (Hidden : Type u₁)
    (anchor : Hidden) :
    ModelObsEq M (hiddenExtensionModel M Hidden) := by
  apply modelObsEq_symm
  exact
    modelObsEq_of_latentCover
      (hiddenExtensionModel M Hidden)
      M
      (hiddenExtensionCover M Hidden anchor)

/--
A hidden-factor extension preserves the possible result set of every
admissible experiment.
-/
theorem hiddenExtensionModel_preserves_experimentOutcomeSet
    {Obs : Type u₂}
    {Result : Type u₃}
    (M : GenerativeModel Obs)
    (Hidden : Type u₁)
    (anchor : Hidden)
    (experiment : AdmissibleExperiment Obs Result) :
    ExperimentOutcomeSet M experiment =
      ExperimentOutcomeSet
        (hiddenExtensionModel M Hidden)
        experiment := by
  exact
    modelObsEq_preserves_experimentOutcomeSet
      M
      (hiddenExtensionModel M Hidden)
      (modelObsEq_hiddenExtensionModel
        M Hidden anchor)
      experiment

/--
No admissible experiment separates a model from an inhabited
hidden-factor extension.
-/
theorem no_experiment_separates_hiddenExtensionModel
    {Obs : Type u₂}
    {Result : Type u₃}
    (M : GenerativeModel Obs)
    (Hidden : Type u₁)
    (anchor : Hidden)
    (experiment : AdmissibleExperiment Obs Result) :
    ¬ ExperimentSeparates
      M
      (hiddenExtensionModel M Hidden)
      experiment := by
  exact
    modelObsEq_prevents_experimental_separation
      M
      (hiddenExtensionModel M Hidden)
      (modelObsEq_hiddenExtensionModel
        M Hidden anchor)
      experiment

/-!
## Hidden distinctions and reconstruction failure
-/

/--
Two different hidden values attached to the same base latent state
produce distinct extended latent states with the same observation.
-/
theorem hiddenExtensionModel_has_latent_collision
    {Obs : Type u₂}
    (M : GenerativeModel Obs)
    (Hidden : Type u₁)
    (x : M.Latent)
    (h₀ h₁ : Hidden)
    (hHiddenDistinct : h₀ ≠ h₁) :
    ∃ a b : (hiddenExtensionModel M Hidden).Latent,
      a ≠ b ∧
        (hiddenExtensionModel M Hidden).observe a =
          (hiddenExtensionModel M Hidden).observe b := by
  refine ⟨(x, h₀), (x, h₁), ?_, rfl⟩
  intro hPair
  apply hHiddenDistinct
  exact congrArg Prod.snd hPair

/--
The observation map of a hidden-factor extension is not injective
whenever the base model has a latent state and the hidden type has two
different values.
-/
theorem hiddenExtensionModel_observe_not_injective
    {Obs : Type u₂}
    (M : GenerativeModel Obs)
    (Hidden : Type u₁)
    (x : M.Latent)
    (h₀ h₁ : Hidden)
    (hHiddenDistinct : h₀ ≠ h₁) :
    ¬ Function.Injective
      (hiddenExtensionModel M Hidden).observe := by
  intro hInjective
  rcases
      hiddenExtensionModel_has_latent_collision
        M Hidden x h₀ h₁ hHiddenDistinct with
    ⟨a, b, hLatentDistinct, hObservation⟩
  apply hLatentDistinct
  exact hInjective hObservation

/--
A hidden-factor extension with a genuine hidden distinction cannot
possess a globally exact latent decoder.
-/
theorem hiddenExtensionModel_has_no_exactLatentDecoder
    {Obs : Type u₂}
    (M : GenerativeModel Obs)
    (Hidden : Type u₁)
    (x : M.Latent)
    (h₀ h₁ : Hidden)
    (hHiddenDistinct : h₀ ≠ h₁) :
    ¬ HasExactLatentDecoder
      (hiddenExtensionModel M Hidden) := by
  intro hDecoder
  have hInjective :
      Function.Injective
        (hiddenExtensionModel M Hidden).observe :=
    exactLatentDecoder_implies_injective
      (hiddenExtensionModel M Hidden)
      hDecoder
  exact
    hiddenExtensionModel_observe_not_injective
      M Hidden x h₀ h₁ hHiddenDistinct
      hInjective

/--
An added hidden distinction is observationally underdetermined.

The extended model is observationally equivalent to the original
model, but its full latent state cannot be reconstructed exactly from
accessible observations.
-/
theorem hidden_factor_is_observationally_underdetermined
    {Obs : Type u₂}
    (M : GenerativeModel Obs)
    (Hidden : Type u₁)
    (x : M.Latent)
    (h₀ h₁ : Hidden)
    (hHiddenDistinct : h₀ ≠ h₁) :
    ModelObsEq M (hiddenExtensionModel M Hidden) ∧
      ¬ HasExactLatentDecoder
        (hiddenExtensionModel M Hidden) := by
  constructor
  · exact
      modelObsEq_hiddenExtensionModel
        M Hidden h₀
  · exact
      hiddenExtensionModel_has_no_exactLatentDecoder
        M Hidden x h₀ h₁ hHiddenDistinct

/--
A hidden-factor extension simultaneously preserves every accessible
experimental outcome and introduces a latent distinction that the
observation map cannot recover.
-/
theorem hidden_factor_is_empirically_invisible
    {Obs : Type u₂}
    {Result : Type u₃}
    (M : GenerativeModel Obs)
    (Hidden : Type u₁)
    (x : M.Latent)
    (h₀ h₁ : Hidden)
    (hHiddenDistinct : h₀ ≠ h₁)
    (experiment : AdmissibleExperiment Obs Result) :
    ExperimentOutcomeSet M experiment =
        ExperimentOutcomeSet
          (hiddenExtensionModel M Hidden)
          experiment ∧
      ¬ Function.Injective
        (hiddenExtensionModel M Hidden).observe := by
  constructor
  · exact
      hiddenExtensionModel_preserves_experimentOutcomeSet
        M Hidden h₀ experiment
  · exact
      hiddenExtensionModel_observe_not_injective
        M Hidden x h₀ h₁ hHiddenDistinct

/--
The earlier duplicated model is the Boolean special case of the
general hidden-factor extension.
-/
theorem duplicateModel_eq_hiddenExtensionModel
    {Obs : Type u₂}
    (M : GenerativeModel Obs) :
    duplicateModel M =
      hiddenExtensionModel M Bool := by
  rfl

/-!
## Observation fibers and arbitrary latent multiplicity

The observation fiber over an accessible observation contains all
latent states that produce that observation.

Hidden-factor extensions show that an observation fiber may contain
arbitrarily many distinct latent states without changing any
observer-accessible experimental outcome.
-/

/--
The latent fiber over `observation` contains every latent state that
produces that observation.
-/
abbrev LatentFiber
    {Obs : Type u₂}
    (M : GenerativeModel Obs)
    (observation : Obs) :=
  {x : M.Latent // M.observe x = observation}

/--
Every hidden value determines a latent state in the fiber over the
observation produced by the fixed base state `x`.
-/
def hiddenValueToFiber
    {Obs : Type u₂}
    (M : GenerativeModel Obs)
    (Hidden : Type u₁)
    (x : M.Latent) :
    Hidden →
      LatentFiber
        (hiddenExtensionModel M Hidden)
        (M.observe x) :=
  fun h => ⟨(x, h), rfl⟩

/--
Different hidden values determine different extended latent states
inside the same observation fiber.
-/
theorem hiddenValueToFiber_injective
    {Obs : Type u₂}
    (M : GenerativeModel Obs)
    (Hidden : Type u₁)
    (x : M.Latent) :
    Function.Injective
      (hiddenValueToFiber M Hidden x) := by
  intro h₀ h₁ hEqual
  have hPair : (x, h₀) = (x, h₁) :=
    congrArg Subtype.val hEqual
  exact congrArg Prod.snd hPair

/--
Every hidden type embeds into an observation fiber of its associated
hidden-factor extension.
-/
def hiddenTypeEmbeddingIntoFiber
    {Obs : Type u₂}
    (M : GenerativeModel Obs)
    (Hidden : Type u₁)
    (x : M.Latent) :
    Hidden ↪
      LatentFiber
        (hiddenExtensionModel M Hidden)
        (M.observe x) where
  toFun := hiddenValueToFiber M Hidden x
  inj' := hiddenValueToFiber_injective M Hidden x

/--
The hidden type places a lower bound on the multiplicity of the
corresponding observation fiber.
-/
theorem hiddenType_injects_into_observationFiber
    {Obs : Type u₂}
    (M : GenerativeModel Obs)
    (Hidden : Type u₁)
    (x : M.Latent) :
    ∃ _ :
        Hidden ↪
          LatentFiber
            (hiddenExtensionModel M Hidden)
            (M.observe x),
      True := by
  exact
    ⟨hiddenTypeEmbeddingIntoFiber M Hidden x,
      True.intro⟩


/-!
## Finite multiplicity models

For each natural number `n`, the finite multiplicity model attaches
`n + 1` hidden copies to every latent state of the original model.
-/

/--
The canonical anchor of the finite hidden type `Fin (n + 1)`.
-/
def finiteMultiplicityAnchor
    (n : Nat) :
    Fin (n + 1) :=
  ⟨0, by omega⟩

/--
The finite multiplicity model attaches `n + 1` hidden copies to every
latent state while preserving the original observation map.
-/
def finiteMultiplicityModel
    {Obs : Type u₂}
    (M : GenerativeModel Obs)
    (n : Nat) :
    GenerativeModel Obs :=
  hiddenExtensionModel M (Fin (n + 1))

/--
The original model is observationally equivalent to every finite
multiplicity model constructed from it.
-/
theorem modelObsEq_finiteMultiplicityModel
    {Obs : Type u₂}
    (M : GenerativeModel Obs)
    (n : Nat) :
    ModelObsEq M (finiteMultiplicityModel M n) := by
  exact
    modelObsEq_hiddenExtensionModel
      M
      (Fin (n + 1))
      (finiteMultiplicityAnchor n)

/--
Every admissible experiment has the same possible outcome set under
the original model and its finite multiplicity extension.
-/
theorem finiteMultiplicityModel_preserves_experimentOutcomeSet
    {Obs : Type u₂}
    {Result : Type u₃}
    (M : GenerativeModel Obs)
    (n : Nat)
    (experiment : AdmissibleExperiment Obs Result) :
    ExperimentOutcomeSet M experiment =
      ExperimentOutcomeSet
        (finiteMultiplicityModel M n)
        experiment := by
  exact
    modelObsEq_preserves_experimentOutcomeSet
      M
      (finiteMultiplicityModel M n)
      (modelObsEq_finiteMultiplicityModel M n)
      experiment

/--
No admissible experiment separates the original model from any of its
finite multiplicity extensions.
-/
theorem no_experiment_separates_finiteMultiplicityModel
    {Obs : Type u₂}
    {Result : Type u₃}
    (M : GenerativeModel Obs)
    (n : Nat)
    (experiment : AdmissibleExperiment Obs Result) :
    ¬ ExperimentSeparates
      M
      (finiteMultiplicityModel M n)
      experiment := by
  exact
    modelObsEq_prevents_experimental_separation
      M
      (finiteMultiplicityModel M n)
      (modelObsEq_finiteMultiplicityModel M n)
      experiment

/-!
## Explicit families of hidden latent states
-/

/--
The finite hidden family associated with a base latent state `x`.
-/
def finiteMultiplicityFamily
    {Obs : Type u₂}
    (M : GenerativeModel Obs)
    (n : Nat)
    (x : M.Latent) :
    Fin (n + 1) →
      (finiteMultiplicityModel M n).Latent :=
  fun i => (x, i)

/--
The finite hidden family is injective.
-/
theorem finiteMultiplicityFamily_injective
    {Obs : Type u₂}
    (M : GenerativeModel Obs)
    (n : Nat)
    (x : M.Latent) :
    Function.Injective
      (finiteMultiplicityFamily M n x) := by
  intro i j hEqual
  exact congrArg Prod.snd hEqual

/--
Every member of the finite hidden family produces the same accessible
observation as the original latent state.
-/
theorem finiteMultiplicityFamily_same_observation
    {Obs : Type u₂}
    (M : GenerativeModel Obs)
    (n : Nat)
    (x : M.Latent)
    (i : Fin (n + 1)) :
    (finiteMultiplicityModel M n).observe
        (finiteMultiplicityFamily M n x i) =
      M.observe x := by
  rfl

/--
Every base latent state generates `n + 1` distinct latent states in
the finite multiplicity model, all producing the same observation.
-/
theorem finiteMultiplicityModel_has_n_succ_hidden_states
    {Obs : Type u₂}
    (M : GenerativeModel Obs)
    (n : Nat)
    (x : M.Latent) :
    ∃ family :
        Fin (n + 1) →
          (finiteMultiplicityModel M n).Latent,
      Function.Injective family ∧
        ∀ i : Fin (n + 1),
          (finiteMultiplicityModel M n).observe
              (family i) =
            M.observe x := by
  refine
    ⟨finiteMultiplicityFamily M n x,
      finiteMultiplicityFamily_injective M n x,
      ?_⟩
  intro i
  exact
    finiteMultiplicityFamily_same_observation
      M n x i

/--
The finite hidden type embeds into the observation fiber over the
observation generated by `x`.
-/
def finiteMultiplicityFiberEmbedding
    {Obs : Type u₂}
    (M : GenerativeModel Obs)
    (n : Nat)
    (x : M.Latent) :
    Fin (n + 1) ↪
      LatentFiber
        (finiteMultiplicityModel M n)
        (M.observe x) :=
  hiddenTypeEmbeddingIntoFiber
    M
    (Fin (n + 1))
    x

/-!
## Reconstruction failure with two or more hidden copies
-/

/--
The first hidden value in a finite multiplicity model containing at
least two hidden copies.
-/
def finiteMultiplicityZero
    (n : Nat) :
    Fin ((n + 1) + 1) :=
  ⟨0, by omega⟩

/--
The second hidden value in a finite multiplicity model containing at
least two hidden copies.
-/
def finiteMultiplicityOne
    (n : Nat) :
    Fin ((n + 1) + 1) :=
  ⟨1, by omega⟩

/--
The first and second hidden values are distinct.
-/
theorem finiteMultiplicityZero_ne_one
    (n : Nat) :
    finiteMultiplicityZero n ≠
      finiteMultiplicityOne n := by
  intro hEqual
  have hValues :
      (finiteMultiplicityZero n).val =
        (finiteMultiplicityOne n).val :=
    congrArg Fin.val hEqual
  change 0 = 1 at hValues
  omega

/--
Every finite multiplicity model with at least two hidden copies has a
non-injective observation map.
-/
theorem finiteMultiplicityModel_observe_not_injective
    {Obs : Type u₂}
    (M : GenerativeModel Obs)
    (n : Nat)
    (x : M.Latent) :
    ¬ Function.Injective
      (finiteMultiplicityModel M (n + 1)).observe := by
  exact
    hiddenExtensionModel_observe_not_injective
      M
      (Fin ((n + 1) + 1))
      x
      (finiteMultiplicityZero n)
      (finiteMultiplicityOne n)
      (finiteMultiplicityZero_ne_one n)

/--
No finite multiplicity model with at least two hidden copies can
possess a globally exact latent decoder.
-/
theorem finiteMultiplicityModel_has_no_exactLatentDecoder
    {Obs : Type u₂}
    (M : GenerativeModel Obs)
    (n : Nat)
    (x : M.Latent) :
    ¬ HasExactLatentDecoder
      (finiteMultiplicityModel M (n + 1)) := by
  intro hDecoder
  have hInjective :
      Function.Injective
        (finiteMultiplicityModel M (n + 1)).observe :=
    exactLatentDecoder_implies_injective
      (finiteMultiplicityModel M (n + 1))
      hDecoder
  exact
    finiteMultiplicityModel_observe_not_injective
      M n x hInjective

/--
A model with at least two finite hidden copies is observationally
equivalent to the original model but does not permit exact latent
reconstruction.
-/
theorem finite_hidden_multiplicity_is_underdetermined
    {Obs : Type u₂}
    (M : GenerativeModel Obs)
    (n : Nat)
    (x : M.Latent) :
    ModelObsEq
        M
        (finiteMultiplicityModel M (n + 1)) ∧
      ¬ HasExactLatentDecoder
        (finiteMultiplicityModel M (n + 1)) := by
  constructor
  · exact
      modelObsEq_finiteMultiplicityModel
        M
        (n + 1)
  · exact
      finiteMultiplicityModel_has_no_exactLatentDecoder
        M n x

/--
For every natural number `n`, the observer-accessible data are
compatible with a model containing `n + 1` distinct latent states in
one observation fiber.
-/
theorem arbitrary_finite_latent_multiplicity
    {Obs : Type u₂}
    (M : GenerativeModel Obs)
    (n : Nat)
    (x : M.Latent) :
    ModelObsEq M (finiteMultiplicityModel M n) ∧
      ∃ family :
          Fin (n + 1) →
            (finiteMultiplicityModel M n).Latent,
        Function.Injective family ∧
          ∀ i : Fin (n + 1),
            (finiteMultiplicityModel M n).observe
                (family i) =
              M.observe x := by
  constructor
  · exact modelObsEq_finiteMultiplicityModel M n
  · exact
      finiteMultiplicityModel_has_n_succ_hidden_states
        M n x

/--
Arbitrarily large finite latent multiplicity is empirically invisible
to every admissible experiment.

For each `n`, an observationally equivalent model contains `n + 1`
distinct latent states producing one common observation, while every
admissible experiment retains exactly the same possible outcomes.
-/
theorem arbitrary_finite_latent_multiplicity_is_empirically_hidden
    {Obs : Type u₂}
    {Result : Type u₃}
    (M : GenerativeModel Obs)
    (n : Nat)
    (x : M.Latent)
    (experiment : AdmissibleExperiment Obs Result) :
    ExperimentOutcomeSet M experiment =
        ExperimentOutcomeSet
          (finiteMultiplicityModel M n)
          experiment ∧
      ∃ family :
          Fin (n + 1) →
            (finiteMultiplicityModel M n).Latent,
        Function.Injective family ∧
          ∀ i : Fin (n + 1),
            (finiteMultiplicityModel M n).observe
                (family i) =
              M.observe x := by
  constructor
  · exact
      finiteMultiplicityModel_preserves_experimentOutcomeSet
        M n experiment
  · exact
      finiteMultiplicityModel_has_n_succ_hidden_states
        M n x
/-!
## Countably infinite latent multiplicity

Finite hidden multiplicity can be extended to countably infinite
multiplicity.

Attaching a natural-number coordinate to every latent state creates
countably many distinct latent states in one observation fiber while
preserving every observer-accessible experimental outcome.
-/

/--
The countable multiplicity model attaches a natural-number coordinate
to every latent state and ignores that coordinate during observation.
-/
def countableMultiplicityModel
    {Obs : Type u₂}
    (M : GenerativeModel Obs) :
    GenerativeModel Obs :=
  hiddenExtensionModel M Nat

/--
The original model is observationally equivalent to its countable
multiplicity extension.
-/
theorem modelObsEq_countableMultiplicityModel
    {Obs : Type u₂}
    (M : GenerativeModel Obs) :
    ModelObsEq M (countableMultiplicityModel M) := by
  exact
    modelObsEq_hiddenExtensionModel
      M Nat 0

/--
A fixed base latent state determines a countable family of extended
latent states.
-/
def countableMultiplicityFamily
    {Obs : Type u₂}
    (M : GenerativeModel Obs)
    (x : M.Latent) :
    Nat → (countableMultiplicityModel M).Latent :=
  fun n => (x, n)

/--
The countable family of extended latent states is injective.
-/
theorem countableMultiplicityFamily_injective
    {Obs : Type u₂}
    (M : GenerativeModel Obs)
    (x : M.Latent) :
    Function.Injective
      (countableMultiplicityFamily M x) := by
  intro m n hEqual
  exact congrArg Prod.snd hEqual

/--
Every member of the countable latent family produces the same
accessible observation.
-/
theorem countableMultiplicityFamily_same_observation
    {Obs : Type u₂}
    (M : GenerativeModel Obs)
    (x : M.Latent)
    (n : Nat) :
    (countableMultiplicityModel M).observe
        (countableMultiplicityFamily M x n) =
      M.observe x := by
  rfl

/--
The natural numbers embed into the observation fiber generated by a
fixed base latent state.
-/
def countableMultiplicityFiberEmbedding
    {Obs : Type u₂}
    (M : GenerativeModel Obs)
    (x : M.Latent) :
    Nat ↪
      LatentFiber
        (countableMultiplicityModel M)
        (M.observe x) where
  toFun n := ⟨(x, n), rfl⟩
  inj' := by
    intro m n hEqual
    have hPair : (x, m) = (x, n) :=
      congrArg Subtype.val hEqual
    exact congrArg Prod.snd hPair

/--
The observation fiber over `M.observe x` contains an embedded copy of
the natural numbers.
-/
theorem countableMultiplicityFiber_contains_nat
    {Obs : Type u₂}
    (M : GenerativeModel Obs)
    (x : M.Latent) :
    Nonempty
      (Nat ↪
        LatentFiber
          (countableMultiplicityModel M)
          (M.observe x)) := by
  exact
    ⟨countableMultiplicityFiberEmbedding M x⟩

/--
Every base latent state generates countably many distinct extended
latent states that all produce the same observation.
-/
theorem countableMultiplicityModel_has_countable_hidden_family
    {Obs : Type u₂}
    (M : GenerativeModel Obs)
    (x : M.Latent) :
    ∃ family :
        Nat → (countableMultiplicityModel M).Latent,
      Function.Injective family ∧
        ∀ n : Nat,
          (countableMultiplicityModel M).observe
              (family n) =
            M.observe x := by
  refine
    ⟨countableMultiplicityFamily M x, ?_, ?_⟩
  · exact countableMultiplicityFamily_injective M x
  · intro n
    exact
      countableMultiplicityFamily_same_observation
        M x n

/-!
## Experimental invariance
-/

/--
Every admissible experiment has the same possible outcome set under
the original model and its countable multiplicity extension.
-/
theorem countableMultiplicityModel_preserves_experimentOutcomeSet
    {Obs : Type u₂}
    {Result : Type u₃}
    (M : GenerativeModel Obs)
    (experiment : AdmissibleExperiment Obs Result) :
    ExperimentOutcomeSet M experiment =
      ExperimentOutcomeSet
        (countableMultiplicityModel M)
        experiment := by
  exact
    modelObsEq_preserves_experimentOutcomeSet
      M
      (countableMultiplicityModel M)
      (modelObsEq_countableMultiplicityModel M)
      experiment

/--
No admissible experiment separates the original model from its
countable multiplicity extension.
-/
theorem no_experiment_separates_countableMultiplicityModel
    {Obs : Type u₂}
    {Result : Type u₃}
    (M : GenerativeModel Obs)
    (experiment : AdmissibleExperiment Obs Result) :
    ¬ ExperimentSeparates
      M
      (countableMultiplicityModel M)
      experiment := by
  exact
    modelObsEq_prevents_experimental_separation
      M
      (countableMultiplicityModel M)
      (modelObsEq_countableMultiplicityModel M)
      experiment

/-!
## Reconstruction failure
-/

/--
The countable multiplicity model has a non-injective observation map
whenever the original model contains a latent state.
-/
theorem countableMultiplicityModel_observe_not_injective
    {Obs : Type u₂}
    (M : GenerativeModel Obs)
    (x : M.Latent) :
    ¬ Function.Injective
      (countableMultiplicityModel M).observe := by
  change
    ¬ Function.Injective
      (hiddenExtensionModel M Nat).observe
  exact
    hiddenExtensionModel_observe_not_injective
      M Nat x 0 1 (by omega)

/--
The countable multiplicity model cannot possess a globally exact
latent decoder whenever the original model contains a latent state.
-/
theorem countableMultiplicityModel_has_no_exactLatentDecoder
    {Obs : Type u₂}
    (M : GenerativeModel Obs)
    (x : M.Latent) :
    ¬ HasExactLatentDecoder
      (countableMultiplicityModel M) := by
  change
    ¬ HasExactLatentDecoder
      (hiddenExtensionModel M Nat)
  exact
    hiddenExtensionModel_has_no_exactLatentDecoder
      M Nat x 0 1 (by omega)

/--
Countably infinite latent multiplicity is observationally
underdetermined.

The extension is observationally equivalent to the original model,
contains a countable family inside one observation fiber, and does not
permit exact latent reconstruction.
-/
theorem countable_latent_multiplicity_is_underdetermined
    {Obs : Type u₂}
    (M : GenerativeModel Obs)
    (x : M.Latent) :
    ModelObsEq M (countableMultiplicityModel M) ∧
      Nonempty
        (Nat ↪
          LatentFiber
            (countableMultiplicityModel M)
            (M.observe x)) ∧
      ¬ HasExactLatentDecoder
        (countableMultiplicityModel M) := by
  constructor
  · exact modelObsEq_countableMultiplicityModel M
  constructor
  · exact countableMultiplicityFiber_contains_nat M x
  · exact
      countableMultiplicityModel_has_no_exactLatentDecoder
        M x

/--
Countably infinite hidden multiplicity is empirically invisible to
every admissible experiment.
-/
theorem countable_latent_multiplicity_is_empirically_hidden
    {Obs : Type u₂}
    {Result : Type u₃}
    (M : GenerativeModel Obs)
    (x : M.Latent)
    (experiment : AdmissibleExperiment Obs Result) :
    ExperimentOutcomeSet M experiment =
        ExperimentOutcomeSet
          (countableMultiplicityModel M)
          experiment ∧
      Nonempty
        (Nat ↪
          LatentFiber
            (countableMultiplicityModel M)
            (M.observe x)) ∧
      ¬ Function.Injective
        (countableMultiplicityModel M).observe := by
  constructor
  · exact
      countableMultiplicityModel_preserves_experimentOutcomeSet
        M experiment
  constructor
  · exact countableMultiplicityFiber_contains_nat M x
  · exact
      countableMultiplicityModel_observe_not_injective
        M x

/-!
## Strict latent covers and the absence of maximal latent models

A strict latent cover contains genuinely different extended latent
states that project to the same base latent state.

Because the projection preserves observations, those additional
latent distinctions remain invisible through the accessible
observation map.
-/

/--
A strict latent cover is a latent cover whose projection is not
injective.
-/
structure StrictLatentCover
    {Obs : Type u₂}
    (Extended Base : GenerativeModel Obs) where
  toLatentCover : LatentCover Extended Base
  project_not_injective :
    ¬ Function.Injective toLatentCover.project

/--
Every strict latent cover is an ordinary latent cover.
-/
def strictLatentCover_is_latentCover
    {Obs : Type u₂}
    {Extended Base : GenerativeModel Obs}
    (cover : StrictLatentCover Extended Base) :
    LatentCover Extended Base :=
  cover.toLatentCover

/--
A strict latent cover is observationally equivalent to its base
model.
-/
theorem modelObsEq_of_strictLatentCover
    {Obs : Type u₂}
    (Extended Base : GenerativeModel Obs)
    (cover : StrictLatentCover Extended Base) :
    ModelObsEq Extended Base := by
  exact
    modelObsEq_of_latentCover
      Extended Base cover.toLatentCover

/--
A strict latent cover preserves the possible outcome set of every
admissible experiment.
-/
theorem strictLatentCover_preserves_experimentOutcomeSet
    {Obs : Type u₂}
    {Result : Type u₃}
    (Extended Base : GenerativeModel Obs)
    (cover : StrictLatentCover Extended Base)
    (experiment : AdmissibleExperiment Obs Result) :
    ExperimentOutcomeSet Extended experiment =
      ExperimentOutcomeSet Base experiment := by
  exact
    latentCover_preserves_experimentOutcomeSet
      Extended Base cover.toLatentCover experiment

/--
No admissible experiment separates a strict latent cover from its
base model.
-/
theorem strictLatentCover_prevents_experimental_separation
    {Obs : Type u₂}
    {Result : Type u₃}
    (Extended Base : GenerativeModel Obs)
    (cover : StrictLatentCover Extended Base)
    (experiment : AdmissibleExperiment Obs Result) :
    ¬ ExperimentSeparates Extended Base experiment := by
  exact
    latentCover_prevents_experimental_separation
      Extended Base cover.toLatentCover experiment

/-!
## Hidden collisions induced by strict covers
-/

/--
The observation map of a strict latent cover is not injective.
-/
theorem strictLatentCover_extended_observe_not_injective
    {Obs : Type u₂}
    (Extended Base : GenerativeModel Obs)
    (cover : StrictLatentCover Extended Base) :
    ¬ Function.Injective Extended.observe := by
  intro hObserveInjective
  apply cover.project_not_injective
  intro x y hProject
  apply hObserveInjective
  calc
    Extended.observe x =
        Base.observe
          (cover.toLatentCover.project x) :=
      cover.toLatentCover.observation_preserved x
    _ =
        Base.observe
          (cover.toLatentCover.project y) :=
      congrArg Base.observe hProject
    _ = Extended.observe y :=
      (cover.toLatentCover.observation_preserved y).symm

/--
A strict latent cover cannot possess a globally exact latent decoder.
-/
theorem strictLatentCover_extended_has_no_exactLatentDecoder
    {Obs : Type u₂}
    (Extended Base : GenerativeModel Obs)
    (cover : StrictLatentCover Extended Base) :
    ¬ HasExactLatentDecoder Extended := by
  intro hDecoder
  have hInjective : Function.Injective Extended.observe :=
    exactLatentDecoder_implies_injective Extended hDecoder
  exact
    strictLatentCover_extended_observe_not_injective
      Extended Base cover hInjective

/--
A strict latent cover contains two distinct extended latent states
that produce the same accessible observation.
-/
theorem strictLatentCover_has_latent_collision
    {Obs : Type u₂}
    (Extended Base : GenerativeModel Obs)
    (cover : StrictLatentCover Extended Base) :
    ∃ x y : Extended.Latent,
      x ≠ y ∧ Extended.observe x = Extended.observe y := by
  classical
  have hNotInjective :
      ¬ Function.Injective cover.toLatentCover.project :=
    cover.project_not_injective
  rw [Function.not_injective_iff] at hNotInjective
  rcases hNotInjective with
    ⟨x, y, hProject, hDistinct⟩
  refine ⟨x, y, hDistinct, ?_⟩
  calc
    Extended.observe x =
        Base.observe
          (cover.toLatentCover.project x) :=
      cover.toLatentCover.observation_preserved x
    _ =
        Base.observe
          (cover.toLatentCover.project y) :=
      congrArg Base.observe hProject
    _ = Extended.observe y :=
      (cover.toLatentCover.observation_preserved y).symm

/-!
## Strict hidden-factor extensions
-/

/--
A hidden-factor extension with two distinct hidden values is a strict
latent cover of the original model.
-/
def hiddenExtensionStrictCover
    {Obs : Type u₂}
    (M : GenerativeModel Obs)
    (Hidden : Type u₁)
    (x : M.Latent)
    (h₀ h₁ : Hidden)
    (hHiddenDistinct : h₀ ≠ h₁) :
    StrictLatentCover
      (hiddenExtensionModel M Hidden)
      M where
  toLatentCover :=
    hiddenExtensionCover M Hidden h₀
  project_not_injective := by
    intro hInjective
    have hPair : (x, h₀) = (x, h₁) := by
      apply hInjective
      rfl
    apply hHiddenDistinct
    exact congrArg Prod.snd hPair

/--
The Boolean extension adds two latent copies of every state while
preserving the original observation.
-/
def booleanExtensionModel
    {Obs : Type u₂}
    (M : GenerativeModel.{u₁, u₂} Obs) :
    GenerativeModel.{u₁, u₂} Obs where
  Latent := M.Latent × Bool
  observe state := M.observe state.1

/--
The Boolean extension is a strict latent cover whenever the original
model contains a latent state.
-/
def booleanExtensionStrictCover
    {Obs : Type u₂}
    (M : GenerativeModel.{u₁, u₂} Obs)
    (x : M.Latent) :
    StrictLatentCover
      (booleanExtensionModel M)
      M where
  toLatentCover := {
    project := fun state => state.1
    project_surjective := by
      intro y
      exact ⟨(y, false), rfl⟩
    observation_preserved := by
      intro state
      rfl
  }
  project_not_injective := by
    intro hInjective
    have hPair : (x, false) = (x, true) := by
      apply hInjective
      rfl
    have hBool : false = true :=
      congrArg Prod.snd hPair
    cases hBool

/--
Every model containing a latent state has a strict hidden extension.
-/
theorem every_inhabited_model_has_strict_hidden_extension
    {Obs : Type u₂}
    (M : GenerativeModel.{u₁, u₂} Obs)
    (x : M.Latent) :
    ∃ Extended : GenerativeModel.{u₁, u₂} Obs,
      Nonempty (StrictLatentCover Extended M) := by
  refine ⟨booleanExtensionModel M, ?_⟩
  exact ⟨booleanExtensionStrictCover M x⟩

/--
Every model containing a latent state has an observationally
equivalent strict latent extension.
-/
theorem every_inhabited_model_has_strict_observational_extension
    {Obs : Type u₂}
    (M : GenerativeModel.{u₁, u₂} Obs)
    (x : M.Latent) :
    ∃ Extended : GenerativeModel.{u₁, u₂} Obs,
      Nonempty (StrictLatentCover Extended M) ∧
        ModelObsEq M Extended := by
  let Extended : GenerativeModel.{u₁, u₂} Obs :=
    booleanExtensionModel M
  have hStrict : StrictLatentCover Extended M := by
    exact booleanExtensionStrictCover M x
  refine ⟨Extended, ⟨hStrict⟩, ?_⟩
  apply modelObsEq_symm
  exact
    modelObsEq_of_strictLatentCover
      Extended M hStrict

/--
Every model containing a latent state has an empirically
indistinguishable strict extension under every fixed admissible
experiment.
-/
theorem every_inhabited_model_has_empirically_hidden_strict_extension
    {Obs : Type u₂}
    {Result : Type u₃}
    (M : GenerativeModel.{u₁, u₂} Obs)
    (x : M.Latent)
    (experiment : AdmissibleExperiment Obs Result) :
    ∃ Extended : GenerativeModel.{u₁, u₂} Obs,
      Nonempty (StrictLatentCover Extended M) ∧
        ExperimentOutcomeSet Extended experiment =
          ExperimentOutcomeSet M experiment := by
  let Extended : GenerativeModel.{u₁, u₂} Obs :=
    booleanExtensionModel M
  have hStrict : StrictLatentCover Extended M := by
    exact booleanExtensionStrictCover M x
  refine ⟨Extended, ⟨hStrict⟩, ?_⟩
  exact
    strictLatentCover_preserves_experimentOutcomeSet
      Extended M hStrict experiment

/-!
## No maximal latent representation
-/

/--
A model is latently maximal when no strict latent cover of that model
exists.
-/
def LatentlyMaximal
    {Obs : Type u₂}
    (M : GenerativeModel.{u₁, u₂} Obs) : Prop :=
  ∀ Extended : GenerativeModel.{u₁, u₂} Obs,
    ¬ Nonempty (StrictLatentCover Extended M)

/--
No model containing a latent state is latently maximal.
-/
theorem no_inhabited_model_is_latentlyMaximal
    {Obs : Type u₂}
    (M : GenerativeModel.{u₁, u₂} Obs)
    (x : M.Latent) :
    ¬ LatentlyMaximal M := by
  intro hMaximal
  apply hMaximal (booleanExtensionModel M)
  exact ⟨booleanExtensionStrictCover M x⟩

/--
There is no observationally maximal latent explanation for an
inhabited model within this framework.

A strict observationally equivalent hidden extension can always be
constructed.
-/
theorem no_maximal_latent_explanation
    {Obs : Type u₂}
    (M : GenerativeModel.{u₁, u₂} Obs)
    (x : M.Latent) :
    ∃ Extended : GenerativeModel.{u₁, u₂} Obs,
      ModelObsEq M Extended ∧
        ¬ HasExactLatentDecoder Extended := by
  let Extended : GenerativeModel.{u₁, u₂} Obs :=
    booleanExtensionModel M
  have hStrict : StrictLatentCover Extended M := by
    exact booleanExtensionStrictCover M x
  refine ⟨Extended, ?_, ?_⟩
  · apply modelObsEq_symm
    exact
      modelObsEq_of_strictLatentCover
        Extended M hStrict
  · exact
      strictLatentCover_extended_has_no_exactLatentDecoder
        Extended M hStrict

/-!
## Observation-invariant properties and empirical identifiability

A property of a generative model is observation-invariant when it has
the same truth value for all observationally equivalent models.

A property determined entirely by the set of reachable observations
must be observation-invariant. Exact latent reconstruction is not
observation-invariant, because an exactly decodable model may have an
observationally equivalent strict hidden extension that is not exactly
decodable.
-/

/--
The reachable observation set of a model contains exactly the
observations produced by at least one latent state.
-/
def ReachableObservationSet
    {Obs : Type u₂}
    (M : GenerativeModel.{u₁, u₂} Obs) :
    Set Obs :=
  {observation | Produces M observation}

/--
Two models are observationally equivalent exactly when their
reachable observation sets are equal.
-/
theorem modelObsEq_iff_reachableObservationSet_eq
    {Obs : Type u₂}
    (M N : GenerativeModel.{u₁, u₂} Obs) :
    ModelObsEq M N ↔
      ReachableObservationSet M =
        ReachableObservationSet N := by
  constructor
  · intro hMN
    ext observation
    exact hMN observation
  · intro hSets observation
    change
      observation ∈ ReachableObservationSet M ↔
        observation ∈ ReachableObservationSet N
    exact Set.ext_iff.mp hSets observation

/--
A model property is observation-invariant when observationally
equivalent models always agree about that property.
-/
def ObservationInvariantProperty
    {Obs : Type u₂}
    (P : GenerativeModel.{u₁, u₂} Obs → Prop) :
    Prop :=
  ∀ M N : GenerativeModel.{u₁, u₂} Obs,
    ModelObsEq M N → (P M ↔ P N)

/--
A model property is determined by reachable observations when some
criterion on observation sets completely determines its truth value.
-/
def DeterminedByReachableObservations
    {Obs : Type u₂}
    (P : GenerativeModel.{u₁, u₂} Obs → Prop) :
    Prop :=
  ∃ criterion : Set Obs → Prop,
    ∀ M : GenerativeModel.{u₁, u₂} Obs,
      P M ↔ criterion (ReachableObservationSet M)

/--
Every property determined by reachable observations is
observation-invariant.
-/
theorem determinedByReachableObservations_implies_invariant
    {Obs : Type u₂}
    (P : GenerativeModel.{u₁, u₂} Obs → Prop)
    (hDetermined : DeterminedByReachableObservations P) :
    ObservationInvariantProperty P := by
  rcases hDetermined with ⟨criterion, hCriterion⟩
  intro M N hMN
  have hSets :
      ReachableObservationSet M =
        ReachableObservationSet N :=
    (modelObsEq_iff_reachableObservationSet_eq M N).mp hMN
  calc
    P M ↔ criterion (ReachableObservationSet M) :=
      hCriterion M
    _ ↔ criterion (ReachableObservationSet N) := by
      rw [hSets]
    _ ↔ P N :=
      (hCriterion N).symm

/-!
## An exactly decodable base model
-/

/--
The identity generative model uses its state directly as its
accessible observation.
-/
def identityGenerativeModel
    (State : Type u₁) :
    GenerativeModel.{u₁, u₁} State where
  Latent := State
  observe := id

/--
The identity generative model possesses a globally exact latent
decoder.
-/
theorem identityGenerativeModel_has_exactLatentDecoder
    (State : Type u₁) :
    HasExactLatentDecoder
      (identityGenerativeModel State) := by
  refine ⟨id, ?_⟩
  intro state
  rfl

/--
The identity model is observationally equivalent to its Boolean
hidden extension.
-/
theorem identityGenerativeModel_modelObsEq_booleanExtension
    (State : Type u₁)
    (x : State) :
    ModelObsEq
      (identityGenerativeModel State)
      (booleanExtensionModel
        (identityGenerativeModel State)) := by
  apply modelObsEq_symm
  exact
    modelObsEq_of_strictLatentCover
      (booleanExtensionModel
        (identityGenerativeModel State))
      (identityGenerativeModel State)
      (booleanExtensionStrictCover
        (identityGenerativeModel State)
        x)

/--
The Boolean hidden extension of the identity model cannot possess an
exact latent decoder.
-/
theorem identityBooleanExtension_has_no_exactLatentDecoder
    (State : Type u₁)
    (x : State) :
    ¬ HasExactLatentDecoder
      (booleanExtensionModel
        (identityGenerativeModel State)) := by
  exact
    strictLatentCover_extended_has_no_exactLatentDecoder
      (booleanExtensionModel
        (identityGenerativeModel State))
      (identityGenerativeModel State)
      (booleanExtensionStrictCover
        (identityGenerativeModel State)
        x)

/-!
## Exact latent reconstruction is not empirically identifiable
-/

/--
Possession of an exact latent decoder is not invariant under
observational equivalence.
-/
theorem exactLatentDecoder_not_observationInvariant
    (State : Type u₁)
    (x : State) :
    ¬ ObservationInvariantProperty
      (fun M : GenerativeModel.{u₁, u₁} State =>
        HasExactLatentDecoder M) := by
  intro hInvariant
  have hEquivalent :
      ModelObsEq
        (identityGenerativeModel State)
        (booleanExtensionModel
          (identityGenerativeModel State)) :=
    identityGenerativeModel_modelObsEq_booleanExtension
      State x
  have hAgreement :
      HasExactLatentDecoder
          (identityGenerativeModel State) ↔
        HasExactLatentDecoder
          (booleanExtensionModel
            (identityGenerativeModel State)) :=
    hInvariant
      (identityGenerativeModel State)
      (booleanExtensionModel
        (identityGenerativeModel State))
      hEquivalent
  have hExtendedDecoder :
      HasExactLatentDecoder
        (booleanExtensionModel
          (identityGenerativeModel State)) :=
    hAgreement.mp
      (identityGenerativeModel_has_exactLatentDecoder State)
  exact
    identityBooleanExtension_has_no_exactLatentDecoder
      State x hExtendedDecoder

/--
Exact latent reconstructability cannot be determined entirely from
the set of reachable observations.
-/
theorem exactLatentDecoder_not_determinedByReachableObservations
    (State : Type u₁)
    (x : State) :
    ¬ DeterminedByReachableObservations
      (fun M : GenerativeModel.{u₁, u₁} State =>
        HasExactLatentDecoder M) := by
  intro hDetermined
  have hInvariant :
      ObservationInvariantProperty
        (fun M : GenerativeModel.{u₁, u₁} State =>
          HasExactLatentDecoder M) :=
    determinedByReachableObservations_implies_invariant
      (fun M : GenerativeModel.{u₁, u₁} State =>
        HasExactLatentDecoder M)
      hDetermined
  exact
    exactLatentDecoder_not_observationInvariant
      State x hInvariant

/-!
## Experimental determination of model properties

A property is determined by an experiment when the set of possible
experimental outcomes completely determines whether the property
holds.

Because observationally equivalent models have identical outcome
sets under every admissible experiment, every experimentally
determined property must be invariant under observational
equivalence.
-/

/--
A model property is determined by an admissible experiment when some
criterion on the experiment's possible outcome set completely
determines whether the property holds.
-/
def DeterminedByExperiment
    {Obs : Type u₂}
    {Result : Type u₃}
    (experiment : AdmissibleExperiment Obs Result)
    (P : GenerativeModel.{u₁, u₂} Obs → Prop) :
    Prop :=
  ∃ criterion : Set Result → Prop,
    ∀ M : GenerativeModel.{u₁, u₂} Obs,
      P M ↔
        criterion
          (ExperimentOutcomeSet M experiment)

/--
Every property determined by an admissible experiment is invariant
under observational equivalence.
-/
theorem determinedByExperiment_implies_invariant
    {Obs : Type u₂}
    {Result : Type u₃}
    (experiment : AdmissibleExperiment Obs Result)
    (P : GenerativeModel.{u₁, u₂} Obs → Prop)
    (hDetermined : DeterminedByExperiment experiment P) :
    ObservationInvariantProperty P := by
  rcases hDetermined with
    ⟨criterion, hCriterion⟩
  intro M N hMN
  have hOutcomes :
      ExperimentOutcomeSet M experiment =
        ExperimentOutcomeSet N experiment :=
    modelObsEq_preserves_experimentOutcomeSet
      M N hMN experiment
  calc
    P M ↔
        criterion
          (ExperimentOutcomeSet M experiment) :=
      hCriterion M
    _ ↔
        criterion
          (ExperimentOutcomeSet N experiment) := by
      rw [hOutcomes]
    _ ↔ P N :=
      (hCriterion N).symm

/-!
## The identity experiment

The identity experiment returns the accessible observation itself.

Its outcome set is therefore exactly the model's reachable
observation set.
-/

/--
The identity experiment returns each accessible observation without
further transformation.
-/
def identityExperiment
    (Obs : Type u₂) :
    AdmissibleExperiment Obs Obs :=
  id

/--
The possible outcomes of the identity experiment are exactly the
reachable observations of the model.
-/
theorem experimentOutcomeSet_identity_eq_reachableObservationSet
    {Obs : Type u₂}
    (M : GenerativeModel.{u₁, u₂} Obs) :
    ExperimentOutcomeSet
        M
        (identityExperiment Obs) =
      ReachableObservationSet M := by
  ext observation
  change
    ExperimentCanProduce
        M
        (identityExperiment Obs)
        observation ↔
      Produces M observation
  rfl

/--
A property is determined by reachable observations exactly when it is
determined by the identity experiment.
-/
theorem determinedByReachableObservations_iff_identityExperiment
    {Obs : Type u₂}
    (P : GenerativeModel.{u₁, u₂} Obs → Prop) :
    DeterminedByReachableObservations P ↔
      DeterminedByExperiment
        (identityExperiment Obs)
        P := by
  constructor
  · rintro ⟨criterion, hCriterion⟩
    refine ⟨criterion, ?_⟩
    intro M
    calc
      P M ↔
          criterion
            (ReachableObservationSet M) :=
        hCriterion M
      _ ↔
          criterion
            (ExperimentOutcomeSet
              M
              (identityExperiment Obs)) := by
        rw [
          experimentOutcomeSet_identity_eq_reachableObservationSet
            M
        ]
  · rintro ⟨criterion, hCriterion⟩
    refine ⟨criterion, ?_⟩
    intro M
    calc
      P M ↔
          criterion
            (ExperimentOutcomeSet
              M
              (identityExperiment Obs)) :=
        hCriterion M
      _ ↔
          criterion
            (ReachableObservationSet M) := by
        rw [
          experimentOutcomeSet_identity_eq_reachableObservationSet
            M
        ]

/-!
## No experiment identifies exact latent reconstruction

Exact latent reconstructability is not invariant under observational
equivalence.

It therefore cannot be determined by any admissible experiment,
regardless of its result type or the criterion applied to its possible
outcomes.
-/

/--
No admissible experiment can determine whether a model possesses a
globally exact latent decoder.
-/
theorem exactLatentDecoder_not_determinedByExperiment
    (State : Type u₁)
    (x : State)
    {Result : Type u₃}
    (experiment : AdmissibleExperiment State Result) :
    ¬ DeterminedByExperiment
      experiment
      (fun M : GenerativeModel.{u₁, u₁} State =>
        HasExactLatentDecoder M) := by
  intro hDetermined
  have hInvariant :
      ObservationInvariantProperty
        (fun M : GenerativeModel.{u₁, u₁} State =>
          HasExactLatentDecoder M) :=
    determinedByExperiment_implies_invariant
      experiment
      (fun M : GenerativeModel.{u₁, u₁} State =>
        HasExactLatentDecoder M)
      hDetermined
  exact
    exactLatentDecoder_not_observationInvariant
      State x hInvariant

/--
No observer-accessible Boolean test can determine whether a model
possesses a globally exact latent decoder.
-/
theorem exactLatentDecoder_not_determinedBy_binaryTest
    (State : Type u₁)
    (x : State)
    (test : AdmissibleExperiment State Bool) :
    ¬ DeterminedByExperiment
      test
      (fun M : GenerativeModel.{u₁, u₁} State =>
        HasExactLatentDecoder M) := by
  exact
    exactLatentDecoder_not_determinedByExperiment
      State x test

/--
Even the identity experiment, which retains every accessible
observation, cannot determine whether exact latent reconstruction is
possible.
-/
theorem exactLatentDecoder_not_determinedBy_identityExperiment
    (State : Type u₁)
    (x : State) :
    ¬ DeterminedByExperiment
      (identityExperiment State)
      (fun M : GenerativeModel.{u₁, u₁} State =>
        HasExactLatentDecoder M) := by
  exact
    exactLatentDecoder_not_determinedByExperiment
      State
      x
      (identityExperiment State)

/-!
## Predicate experiments and complete observational profiles

An observer-accessible predicate asks whether a reachable observation
satisfies some proposition.

The collection of all such predicate experiments completely
characterizes observational equivalence. Two models agree on every
observer-accessible predicate exactly when they produce the same
reachable observations.
-/

/--
A predicate can succeed under a model when at least one latent state
produces an observation satisfying that predicate.
-/
def PredicateCanSucceed
    {Obs : Type u₂}
    (M : GenerativeModel.{u₁, u₂} Obs)
    (predicate : Obs → Prop) : Prop :=
  ∃ x : M.Latent, predicate (M.observe x)

/--
Two models are predicate-equivalent when every observer-accessible
predicate can succeed under one model exactly when it can succeed
under the other.
-/
def PredicateExperimentallyEquivalent
    {Obs : Type u₂}
    (M N : GenerativeModel.{u₁, u₂} Obs) : Prop :=
  ∀ predicate : Obs → Prop,
    PredicateCanSucceed M predicate ↔
      PredicateCanSucceed N predicate

/--
Observationally equivalent models agree on every observer-accessible
predicate experiment.
-/
theorem modelObsEq_implies_predicateExperimentalEquivalence
    {Obs : Type u₂}
    (M N : GenerativeModel.{u₁, u₂} Obs)
    (hMN : ModelObsEq M N) :
    PredicateExperimentallyEquivalent M N := by
  intro predicate
  constructor
  · rintro ⟨x, hx⟩
    have hProduced :
        Produces M (M.observe x) := by
      exact ⟨x, rfl⟩
    rcases (hMN (M.observe x)).mp hProduced with
      ⟨y, hy⟩
    refine ⟨y, ?_⟩
    rw [hy]
    exact hx
  · rintro ⟨y, hy⟩
    have hProduced :
        Produces N (N.observe y) := by
      exact ⟨y, rfl⟩
    rcases (hMN (N.observe y)).mpr hProduced with
      ⟨x, hx⟩
    refine ⟨x, ?_⟩
    rw [hx]
    exact hy

/--
Agreement on every observer-accessible predicate implies
observational equivalence.
-/
theorem predicateExperimentalEquivalence_implies_modelObsEq
    {Obs : Type u₂}
    (M N : GenerativeModel.{u₁, u₂} Obs)
    (hPredicates :
      PredicateExperimentallyEquivalent M N) :
    ModelObsEq M N := by
  intro observation
  constructor
  · rintro ⟨x, hx⟩
    have hSuccess :
        PredicateCanSucceed
          M
          (fun accessible => accessible = observation) := by
      exact ⟨x, hx⟩
    rcases
        (hPredicates
          (fun accessible => accessible = observation)).mp
          hSuccess with
      ⟨y, hy⟩
    exact ⟨y, hy⟩
  · rintro ⟨y, hy⟩
    have hSuccess :
        PredicateCanSucceed
          N
          (fun accessible => accessible = observation) := by
      exact ⟨y, hy⟩
    rcases
        (hPredicates
          (fun accessible => accessible = observation)).mpr
          hSuccess with
      ⟨x, hx⟩
    exact ⟨x, hx⟩

/--
Two models are observationally equivalent exactly when they agree on
every observer-accessible predicate experiment.
-/
theorem modelObsEq_iff_predicateExperimentalEquivalence
    {Obs : Type u₂}
    (M N : GenerativeModel.{u₁, u₂} Obs) :
    ModelObsEq M N ↔
      PredicateExperimentallyEquivalent M N := by
  constructor
  · exact
      modelObsEq_implies_predicateExperimentalEquivalence
        M N
  · exact
      predicateExperimentalEquivalence_implies_modelObsEq
        M N

/-!
## Predicate profiles
-/

/--
The predicate profile of a model records which observer-accessible
predicates can succeed under that model.
-/
def PredicateProfile
    {Obs : Type u₂}
    (M : GenerativeModel.{u₁, u₂} Obs) :
    (Obs → Prop) → Prop :=
  fun predicate => PredicateCanSucceed M predicate

/--
Observationally equivalent models have equal predicate profiles.
-/
theorem modelObsEq_implies_predicateProfile_eq
    {Obs : Type u₂}
    (M N : GenerativeModel.{u₁, u₂} Obs)
    (hMN : ModelObsEq M N) :
    PredicateProfile M = PredicateProfile N := by
  funext predicate
  apply propext
  exact
    (modelObsEq_implies_predicateExperimentalEquivalence
      M N hMN)
      predicate

/--
Equal predicate profiles imply observational equivalence.
-/
theorem predicateProfile_eq_implies_modelObsEq
    {Obs : Type u₂}
    (M N : GenerativeModel.{u₁, u₂} Obs)
    (hProfiles :
      PredicateProfile M = PredicateProfile N) :
    ModelObsEq M N := by
  apply
    predicateExperimentalEquivalence_implies_modelObsEq
      M N
  intro predicate
  have hPoint :
      PredicateProfile M predicate =
        PredicateProfile N predicate :=
    congrArg
      (fun profile => profile predicate)
      hProfiles
  exact Iff.of_eq hPoint

/--
Two models are observationally equivalent exactly when their complete
predicate profiles are equal.
-/
theorem modelObsEq_iff_predicateProfile_eq
    {Obs : Type u₂}
    (M N : GenerativeModel.{u₁, u₂} Obs) :
    ModelObsEq M N ↔
      PredicateProfile M = PredicateProfile N := by
  constructor
  · exact modelObsEq_implies_predicateProfile_eq M N
  · exact predicateProfile_eq_implies_modelObsEq M N

/-!
## Properties determined by complete predicate profiles
-/

/--
A model property is determined by the complete predicate profile when
some criterion on that profile completely determines whether the
property holds.
-/
def DeterminedByPredicateProfile
    {Obs : Type u₂}
    (P : GenerativeModel.{u₁, u₂} Obs → Prop) :
    Prop :=
  ∃ criterion : ((Obs → Prop) → Prop) → Prop,
    ∀ M : GenerativeModel.{u₁, u₂} Obs,
      P M ↔ criterion (PredicateProfile M)

/--
Every property determined by the complete predicate profile is
invariant under observational equivalence.
-/
theorem determinedByPredicateProfile_implies_invariant
    {Obs : Type u₂}
    (P : GenerativeModel.{u₁, u₂} Obs → Prop)
    (hDetermined : DeterminedByPredicateProfile P) :
    ObservationInvariantProperty P := by
  rcases hDetermined with
    ⟨criterion, hCriterion⟩
  intro M N hMN
  have hProfiles :
      PredicateProfile M =
        PredicateProfile N :=
    modelObsEq_implies_predicateProfile_eq
      M N hMN
  calc
    P M ↔ criterion (PredicateProfile M) :=
      hCriterion M
    _ ↔ criterion (PredicateProfile N) := by
      rw [hProfiles]
    _ ↔ P N :=
      (hCriterion N).symm

/--
Exact latent reconstructability cannot be determined even from the
complete collection of observer-accessible predicate experiments.
-/
theorem exactLatentDecoder_not_determinedByPredicateProfile
    (State : Type u₁)
    (x : State) :
    ¬ DeterminedByPredicateProfile
      (fun M : GenerativeModel.{u₁, u₁} State =>
        HasExactLatentDecoder M) := by
  intro hDetermined
  have hInvariant :
      ObservationInvariantProperty
        (fun M : GenerativeModel.{u₁, u₁} State =>
          HasExactLatentDecoder M) :=
    determinedByPredicateProfile_implies_invariant
      (fun M : GenerativeModel.{u₁, u₁} State =>
        HasExactLatentDecoder M)
      hDetermined
  exact
    exactLatentDecoder_not_observationInvariant
      State x hInvariant

/-!
## Complete characterization of empirically determined properties

Reachable observation sets and complete predicate profiles are not
merely necessary sources of empirical information. They are complete
for observationally invariant model properties.

A property is observationally invariant exactly when it can be
determined from the reachable observation set, and exactly when it can
be determined from the complete predicate profile.
-/

/--
Every observationally invariant property can be determined from the
reachable observation set.
-/
theorem invariant_implies_determinedByReachableObservations
    {Obs : Type u₂}
    (P : GenerativeModel.{u₁, u₂} Obs → Prop)
    (hInvariant : ObservationInvariantProperty P) :
    DeterminedByReachableObservations P := by
  refine
    ⟨fun observations =>
      ∃ M : GenerativeModel.{u₁, u₂} Obs,
        ReachableObservationSet M = observations ∧ P M,
      ?_⟩
  intro M
  constructor
  · intro hPM
    exact ⟨M, rfl, hPM⟩
  · rintro ⟨N, hSets, hPN⟩
    have hMN : ModelObsEq M N := by
      apply
        (modelObsEq_iff_reachableObservationSet_eq
          M N).2
      exact hSets.symm
    exact (hInvariant M N hMN).mpr hPN

/--
A property is observationally invariant exactly when it is determined
by the reachable observation set.
-/
theorem observationInvariant_iff_determinedByReachableObservations
    {Obs : Type u₂}
    (P : GenerativeModel.{u₁, u₂} Obs → Prop) :
    ObservationInvariantProperty P ↔
      DeterminedByReachableObservations P := by
  constructor
  · exact
      invariant_implies_determinedByReachableObservations
        P
  · exact
      determinedByReachableObservations_implies_invariant
        P

/--
Every observationally invariant property can be determined from the
complete predicate profile.
-/
theorem invariant_implies_determinedByPredicateProfile
    {Obs : Type u₂}
    (P : GenerativeModel.{u₁, u₂} Obs → Prop)
    (hInvariant : ObservationInvariantProperty P) :
    DeterminedByPredicateProfile P := by
  refine
    ⟨fun profile =>
      ∃ M : GenerativeModel.{u₁, u₂} Obs,
        PredicateProfile M = profile ∧ P M,
      ?_⟩
  intro M
  constructor
  · intro hPM
    exact ⟨M, rfl, hPM⟩
  · rintro ⟨N, hProfiles, hPN⟩
    have hMN : ModelObsEq M N := by
      apply
        (modelObsEq_iff_predicateProfile_eq
          M N).2
      exact hProfiles.symm
    exact (hInvariant M N hMN).mpr hPN

/--
A property is observationally invariant exactly when it is determined
by the complete predicate profile.
-/
theorem observationInvariant_iff_determinedByPredicateProfile
    {Obs : Type u₂}
    (P : GenerativeModel.{u₁, u₂} Obs → Prop) :
    ObservationInvariantProperty P ↔
      DeterminedByPredicateProfile P := by
  constructor
  · exact
      invariant_implies_determinedByPredicateProfile
        P
  · exact
      determinedByPredicateProfile_implies_invariant
        P

/--
Determination by reachable observations is equivalent to
determination by the complete predicate profile.
-/
theorem determinedByReachableObservations_iff_determinedByPredicateProfile
    {Obs : Type u₂}
    (P : GenerativeModel.{u₁, u₂} Obs → Prop) :
    DeterminedByReachableObservations P ↔
      DeterminedByPredicateProfile P := by
  constructor
  · intro hReachable
    have hInvariant : ObservationInvariantProperty P :=
      determinedByReachableObservations_implies_invariant
        P hReachable
    exact
      invariant_implies_determinedByPredicateProfile
        P hInvariant
  · intro hProfile
    have hInvariant : ObservationInvariantProperty P :=
      determinedByPredicateProfile_implies_invariant
        P hProfile
    exact
      invariant_implies_determinedByReachableObservations
        P hInvariant

/-!
## Empirically identifiable properties
-/

/--
A model property is empirically identifiable when its truth value is
fully determined by the complete observer-accessible predicate
profile.
-/
def EmpiricallyIdentifiableProperty
    {Obs : Type u₂}
    (P : GenerativeModel.{u₁, u₂} Obs → Prop) :
    Prop :=
  DeterminedByPredicateProfile P

/--
Empirical identifiability is equivalent to invariance under
observational equivalence.
-/
theorem empiricallyIdentifiable_iff_observationInvariant
    {Obs : Type u₂}
    (P : GenerativeModel.{u₁, u₂} Obs → Prop) :
    EmpiricallyIdentifiableProperty P ↔
      ObservationInvariantProperty P := by
  constructor
  · intro hIdentifiable
    exact
      determinedByPredicateProfile_implies_invariant
        P hIdentifiable
  · intro hInvariant
    exact
      invariant_implies_determinedByPredicateProfile
        P hInvariant

/--
Observationally equivalent models agree on every empirically
identifiable property.
-/
theorem empiricallyIdentifiableProperty_agrees_on_modelObsEq
    {Obs : Type u₂}
    (P : GenerativeModel.{u₁, u₂} Obs → Prop)
    (hIdentifiable : EmpiricallyIdentifiableProperty P)
    (M N : GenerativeModel.{u₁, u₂} Obs)
    (hMN : ModelObsEq M N) :
    P M ↔ P N := by
  have hInvariant : ObservationInvariantProperty P :=
    determinedByPredicateProfile_implies_invariant
      P hIdentifiable
  exact hInvariant M N hMN

/-!
## Property variation obstructs empirical determination

When two observationally equivalent models disagree about a property,
that property cannot be determined by any complete
observer-accessible description.
-/

/--
A property that differs between observationally equivalent models is
not observationally invariant.
-/
theorem property_variation_prevents_observationInvariance
    {Obs : Type u₂}
    (P : GenerativeModel.{u₁, u₂} Obs → Prop)
    (M N : GenerativeModel.{u₁, u₂} Obs)
    (hMN : ModelObsEq M N)
    (hDisagreement : ¬ (P M ↔ P N)) :
    ¬ ObservationInvariantProperty P := by
  intro hInvariant
  exact hDisagreement (hInvariant M N hMN)

/--
A property that differs between observationally equivalent models
cannot be determined by reachable observations.
-/
theorem property_variation_prevents_reachableDetermination
    {Obs : Type u₂}
    (P : GenerativeModel.{u₁, u₂} Obs → Prop)
    (M N : GenerativeModel.{u₁, u₂} Obs)
    (hMN : ModelObsEq M N)
    (hDisagreement : ¬ (P M ↔ P N)) :
    ¬ DeterminedByReachableObservations P := by
  intro hDetermined
  have hInvariant : ObservationInvariantProperty P :=
    determinedByReachableObservations_implies_invariant
      P hDetermined
  exact hDisagreement (hInvariant M N hMN)

/--
A property that differs between observationally equivalent models
cannot be determined by the complete predicate profile.
-/
theorem property_variation_prevents_predicateProfileDetermination
    {Obs : Type u₂}
    (P : GenerativeModel.{u₁, u₂} Obs → Prop)
    (M N : GenerativeModel.{u₁, u₂} Obs)
    (hMN : ModelObsEq M N)
    (hDisagreement : ¬ (P M ↔ P N)) :
    ¬ DeterminedByPredicateProfile P := by
  intro hDetermined
  have hInvariant : ObservationInvariantProperty P :=
    determinedByPredicateProfile_implies_invariant
      P hDetermined
  exact hDisagreement (hInvariant M N hMN)

/--
A property that differs between observationally equivalent models is
not empirically identifiable.
-/
theorem property_variation_prevents_empiricalIdentifiability
    {Obs : Type u₂}
    (P : GenerativeModel.{u₁, u₂} Obs → Prop)
    (M N : GenerativeModel.{u₁, u₂} Obs)
    (hMN : ModelObsEq M N)
    (hDisagreement : ¬ (P M ↔ P N)) :
    ¬ EmpiricallyIdentifiableProperty P := by
  exact
    property_variation_prevents_predicateProfileDetermination
      P M N hMN hDisagreement

/-!
## Exact latent reconstruction as a general obstruction
-/

/--
Exact latent reconstructability is not an empirically identifiable
model property.
-/
theorem exactLatentDecoder_not_empiricallyIdentifiable
    (State : Type u₁)
    (x : State) :
    ¬ EmpiricallyIdentifiableProperty
      (fun M : GenerativeModel.{u₁, u₁} State =>
        HasExactLatentDecoder M) := by
  exact
    exactLatentDecoder_not_determinedByPredicateProfile
      State x

/--
No complete observer-accessible characterization can decide exact
latent reconstructability for all models.
-/
theorem no_complete_observational_criterion_for_exactLatentDecoder
    (State : Type u₁)
    (x : State) :
    ¬ DeterminedByReachableObservations
        (fun M : GenerativeModel.{u₁, u₁} State =>
          HasExactLatentDecoder M) ∧
      ¬ DeterminedByPredicateProfile
        (fun M : GenerativeModel.{u₁, u₁} State =>
          HasExactLatentDecoder M) := by
  constructor
  · exact
      exactLatentDecoder_not_determinedByReachableObservations
        State x
  · exact
      exactLatentDecoder_not_determinedByPredicateProfile
        State x

/-!
## The empirical quotient of generative models

Observational equivalence partitions generative models into classes
that contain exactly the same observer-accessible information.

The empirical model quotient represents models only up to
observational equivalence. Distinct latent explanations belong to the
same empirical class whenever they generate the same reachable
observations.
-/

/--
Observational equivalence defines a setoid on generative models.
-/
def modelObsSetoid
    (Obs : Type u₂) :
    Setoid (GenerativeModel.{u₁, u₂} Obs) where
  r := fun M N => ModelObsEq M N
  iseqv := {
    refl := fun M => modelObsEq_refl M
    symm := fun hMN => modelObsEq_symm hMN
    trans := fun hMN hNK => modelObsEq_trans hMN hNK
  }

/--
The empirical model quotient identifies observationally equivalent
generative models.
-/
abbrev EmpiricalModelQuotient
    (Obs : Type u₂) :
    Type (max (u₁ + 1) u₂) :=
  Quotient
    (modelObsSetoid Obs :
      Setoid (GenerativeModel.{u₁, u₂} Obs))

/--
The canonical projection sends a generative model to its empirical
equivalence class.
-/
def empiricalModelClass
    {Obs : Type u₂}
    (M : GenerativeModel.{u₁, u₂} Obs) :
    EmpiricalModelQuotient.{u₁, u₂} Obs :=
  Quotient.mk
    (modelObsSetoid Obs :
      Setoid (GenerativeModel.{u₁, u₂} Obs))
    M

/--
Two canonical empirical classes are equal exactly when their models
are observationally equivalent.
-/
theorem empiricalModelClass_eq_iff_modelObsEq
    {Obs : Type u₂}
    (M N : GenerativeModel.{u₁, u₂} Obs) :
    empiricalModelClass M = empiricalModelClass N ↔
      ModelObsEq M N := by
  change
    Quotient.mk
          (modelObsSetoid Obs :
            Setoid (GenerativeModel.{u₁, u₂} Obs))
          M =
        Quotient.mk
          (modelObsSetoid Obs :
            Setoid (GenerativeModel.{u₁, u₂} Obs))
          N ↔
      (modelObsSetoid Obs :
        Setoid (GenerativeModel.{u₁, u₂} Obs)).r M N
  exact Quotient.eq

/--
Every empirical equivalence class has a representative generative
model.
-/
theorem empiricalModelClass_surjective
    {Obs : Type u₂} :
    Function.Surjective
      (empiricalModelClass :
        GenerativeModel.{u₁, u₂} Obs →
          EmpiricalModelQuotient.{u₁, u₂} Obs) := by
  intro empiricalClass
  refine Quotient.inductionOn empiricalClass ?_
  intro M
  exact ⟨M, rfl⟩

/-!
## Descent of observationally invariant properties

An observationally invariant property assigns the same truth value to
every model in an empirical equivalence class.

Such a property therefore determines a well-defined proposition on
the empirical model quotient.
-/

/--
An observationally invariant model property descends to a
well-defined property on empirical equivalence classes.
-/
def descendInvariantProperty
    {Obs : Type u₂}
    (P : GenerativeModel.{u₁, u₂} Obs → Prop)
    (hInvariant : ObservationInvariantProperty P) :
    EmpiricalModelQuotient.{u₁, u₂} Obs → Prop :=
  Quotient.lift P (by
    intro M N hMN
    apply propext
    change ModelObsEq M N at hMN
    exact hInvariant M N hMN)

/--
The descended property evaluated on the class of a model agrees with
the original property evaluated on that model.
-/
@[simp]
theorem descendInvariantProperty_empiricalModelClass
    {Obs : Type u₂}
    (P : GenerativeModel.{u₁, u₂} Obs → Prop)
    (hInvariant : ObservationInvariantProperty P)
    (M : GenerativeModel.{u₁, u₂} Obs) :
    descendInvariantProperty P hInvariant
        (empiricalModelClass M) =
      P M := by
  simp [descendInvariantProperty, empiricalModelClass]

/--
A property on the empirical quotient is uniquely determined by its
values on canonical model classes.
-/
theorem descendInvariantProperty_unique
    {Obs : Type u₂}
    (P : GenerativeModel.{u₁, u₂} Obs → Prop)
    (hInvariant : ObservationInvariantProperty P)
    (Q : EmpiricalModelQuotient.{u₁, u₂} Obs → Prop)
    (hQ :
      ∀ M : GenerativeModel.{u₁, u₂} Obs,
        Q (empiricalModelClass M) ↔ P M) :
    Q = descendInvariantProperty P hInvariant := by
  funext empiricalClass
  apply propext
  refine Quotient.inductionOn empiricalClass ?_
  intro M
  change
    Q (empiricalModelClass M) ↔
      descendInvariantProperty P hInvariant
        (empiricalModelClass M)
  rw [descendInvariantProperty_empiricalModelClass]
  exact hQ M

/--
Every observationally invariant property has a unique representation
on the empirical model quotient.
-/
theorem empiricalModelQuotient_universal_property
    {Obs : Type u₂}
    (P : GenerativeModel.{u₁, u₂} Obs → Prop)
    (hInvariant : ObservationInvariantProperty P) :
    ∃! Q : EmpiricalModelQuotient.{u₁, u₂} Obs → Prop,
      ∀ M : GenerativeModel.{u₁, u₂} Obs,
        Q (empiricalModelClass M) ↔ P M := by
  refine
    ⟨descendInvariantProperty P hInvariant, ?_, ?_⟩
  · intro M
    simp
  · intro Q hQ
    exact
      descendInvariantProperty_unique
        P hInvariant Q hQ

/-!
## Pullback from the empirical quotient

Every property defined directly on empirical equivalence classes
produces an observationally invariant property of generative models.
-/

/--
A property on empirical equivalence classes pulls back to a property
of generative models.
-/
def pullbackEmpiricalProperty
    {Obs : Type u₂}
    (Q : EmpiricalModelQuotient.{u₁, u₂} Obs → Prop) :
    GenerativeModel.{u₁, u₂} Obs → Prop :=
  fun M => Q (empiricalModelClass M)

/--
Every property pulled back from the empirical quotient is
observationally invariant.
-/
theorem pullbackEmpiricalProperty_invariant
    {Obs : Type u₂}
    (Q : EmpiricalModelQuotient.{u₁, u₂} Obs → Prop) :
    ObservationInvariantProperty
      (pullbackEmpiricalProperty Q) := by
  intro M N hMN
  unfold pullbackEmpiricalProperty
  have hClass :
      empiricalModelClass M =
        empiricalModelClass N :=
    (empiricalModelClass_eq_iff_modelObsEq M N).2 hMN
  rw [hClass]

/-!
## Factorization through empirical equivalence classes
-/

/--
A model property factors through the empirical quotient when its truth
value depends only on the empirical equivalence class of the model.
-/
def FactorsThroughEmpiricalModelQuotient
    {Obs : Type u₂}
    (P : GenerativeModel.{u₁, u₂} Obs → Prop) :
    Prop :=
  ∃ Q : EmpiricalModelQuotient.{u₁, u₂} Obs → Prop,
    ∀ M : GenerativeModel.{u₁, u₂} Obs,
      P M ↔ Q (empiricalModelClass M)

/--
A model property is observationally invariant exactly when it factors
through the empirical model quotient.
-/
theorem observationInvariant_iff_factorsThroughEmpiricalModelQuotient
    {Obs : Type u₂}
    (P : GenerativeModel.{u₁, u₂} Obs → Prop) :
    ObservationInvariantProperty P ↔
      FactorsThroughEmpiricalModelQuotient P := by
  constructor
  · intro hInvariant
    refine
      ⟨descendInvariantProperty P hInvariant, ?_⟩
    intro M
    simp
  · rintro ⟨Q, hFactor⟩
    intro M N hMN
    have hClass :
        empiricalModelClass M =
          empiricalModelClass N :=
      (empiricalModelClass_eq_iff_modelObsEq M N).2 hMN
    calc
      P M ↔ Q (empiricalModelClass M) :=
        hFactor M
      _ ↔ Q (empiricalModelClass N) := by
        rw [hClass]
      _ ↔ P N :=
        (hFactor N).symm

/--
Empirical identifiability is equivalent to factorization through the
empirical model quotient.
-/
theorem empiricallyIdentifiable_iff_factorsThroughEmpiricalModelQuotient
    {Obs : Type u₂}
    (P : GenerativeModel.{u₁, u₂} Obs → Prop) :
    EmpiricallyIdentifiableProperty P ↔
      FactorsThroughEmpiricalModelQuotient P := by
  constructor
  · intro hIdentifiable
    have hInvariant :
        ObservationInvariantProperty P :=
      (empiricallyIdentifiable_iff_observationInvariant
        P).mp hIdentifiable
    exact
      (observationInvariant_iff_factorsThroughEmpiricalModelQuotient
        P).mp hInvariant
  · intro hFactor
    have hInvariant :
        ObservationInvariantProperty P :=
      (observationInvariant_iff_factorsThroughEmpiricalModelQuotient
        P).mpr hFactor
    exact
      (empiricallyIdentifiable_iff_observationInvariant
        P).mpr hInvariant

/-!
## Exact latent reconstruction does not descend

Exact latent reconstructability varies within a single empirical
equivalence class. It therefore cannot define a property on the
empirical model quotient.
-/

/--
Exact latent reconstructability does not factor through empirical
equivalence classes.
-/
theorem exactLatentDecoder_not_factorsThroughEmpiricalModelQuotient
    (State : Type u₁)
    (x : State) :
    ¬ FactorsThroughEmpiricalModelQuotient
        (fun M : GenerativeModel.{u₁, u₁} State =>
          HasExactLatentDecoder M) := by
  intro hFactor
  have hInvariant :
      ObservationInvariantProperty
        (fun M : GenerativeModel.{u₁, u₁} State =>
          HasExactLatentDecoder M) :=
    (observationInvariant_iff_factorsThroughEmpiricalModelQuotient
      (fun M : GenerativeModel.{u₁, u₁} State =>
        HasExactLatentDecoder M)).mpr hFactor
  exact
    exactLatentDecoder_not_observationInvariant
      State x hInvariant

/--
No property on empirical equivalence classes can recover exact latent
reconstructability for every generative model.
-/
theorem no_empiricalQuotient_property_for_exactLatentDecoder
    (State : Type u₁)
    (x : State) :
    ¬ ∃ Q :
        EmpiricalModelQuotient.{u₁, u₁} State → Prop,
      ∀ M : GenerativeModel.{u₁, u₁} State,
        HasExactLatentDecoder M ↔
          Q (empiricalModelClass M) := by
  exact
    exactLatentDecoder_not_factorsThroughEmpiricalModelQuotient
      State x

/-!
## Realizable observation sets and canonical empirical representation

The empirical equivalence class of a generative model is completely
determined by the set of observations that the model can produce.

The empirical model quotient is therefore equivalent to the type of
reachable-observation sets that are realized by at least one
generative model.
-/

/--
The reachable-observation set descends to a well-defined function on
the empirical model quotient.
-/
def empiricalReachableObservationSet
    {Obs : Type u₂} :
    EmpiricalModelQuotient.{u₁, u₂} Obs → Set Obs :=
  Quotient.lift
    ReachableObservationSet
    (by
      intro M N hMN
      change ModelObsEq M N at hMN
      exact
        (modelObsEq_iff_reachableObservationSet_eq
          M N).mp hMN)

/--
The reachable-observation set associated with the empirical class of
a model is the reachable-observation set of that model.
-/
@[simp]
theorem empiricalReachableObservationSet_empiricalModelClass
    {Obs : Type u₂}
    (M : GenerativeModel.{u₁, u₂} Obs) :
    empiricalReachableObservationSet
        (empiricalModelClass M) =
      ReachableObservationSet M := by
  rfl

/--
Two empirical model classes are equal exactly when their models have
equal reachable-observation sets.
-/
theorem empiricalModelClass_eq_iff_reachableObservationSet_eq
    {Obs : Type u₂}
    (M N : GenerativeModel.{u₁, u₂} Obs) :
    empiricalModelClass M = empiricalModelClass N ↔
      ReachableObservationSet M =
        ReachableObservationSet N := by
  exact
    (empiricalModelClass_eq_iff_modelObsEq M N).trans
      (modelObsEq_iff_reachableObservationSet_eq M N)

/--
The reachable-observation-set representation of empirical classes is
injective.
-/
theorem empiricalReachableObservationSet_injective
    {Obs : Type u₂} :
    Function.Injective
      (empiricalReachableObservationSet :
        EmpiricalModelQuotient.{u₁, u₂} Obs →
          Set Obs) := by
  intro a b
  refine Quotient.inductionOn a ?_
  intro M
  refine Quotient.inductionOn b ?_
  intro N hSets
  change
    empiricalModelClass M =
      empiricalModelClass N
  apply
    (empiricalModelClass_eq_iff_reachableObservationSet_eq
      M N).2
  simpa
      [empiricalReachableObservationSet, empiricalModelClass]
    using hSets

/-!
## Realizable reachable-observation sets
-/

/--
A realizable observation set is a set of accessible observations that
is the reachable-observation set of at least one generative model.
-/
abbrev RealizableObservationSet
    (Obs : Type u₂) :=
  {observations : Set Obs //
    ∃ M : GenerativeModel.{u₁, u₂} Obs,
      ReachableObservationSet M = observations}

/--
Every empirical model class determines a realizable
reachable-observation set.
-/
def empiricalClassToRealizableObservationSet
    {Obs : Type u₂}
    (empiricalClass :
      EmpiricalModelQuotient.{u₁, u₂} Obs) :
    RealizableObservationSet.{u₁, u₂} Obs :=
  ⟨empiricalReachableObservationSet empiricalClass, by
    refine Quotient.inductionOn empiricalClass ?_
    intro M
    refine ⟨M, ?_⟩
    exact
      (empiricalReachableObservationSet_empiricalModelClass
        M).symm⟩

/--
The underlying set of the realizable observation set associated with
a model class is the reachable-observation set of that model.
-/
@[simp]
theorem empiricalClassToRealizableObservationSet_val
    {Obs : Type u₂}
    (M : GenerativeModel.{u₁, u₂} Obs) :
    (empiricalClassToRealizableObservationSet
        (empiricalModelClass M)).1 =
      ReachableObservationSet M := by
  exact
    empiricalReachableObservationSet_empiricalModelClass M

/--
The map from empirical model classes to realizable observation sets
is injective.
-/
theorem empiricalClassToRealizableObservationSet_injective
    {Obs : Type u₂} :
    Function.Injective
      (empiricalClassToRealizableObservationSet :
        EmpiricalModelQuotient.{u₁, u₂} Obs →
          RealizableObservationSet.{u₁, u₂} Obs) := by
  intro a b hEqual
  apply empiricalReachableObservationSet_injective
  have hValues :
      (empiricalClassToRealizableObservationSet a).1 =
        (empiricalClassToRealizableObservationSet b).1 :=
    congrArg
      (fun observations => observations.1)
      hEqual
  simpa [empiricalClassToRealizableObservationSet] using hValues

/--
Every realizable observation set is represented by an empirical model
class.
-/
theorem empiricalClassToRealizableObservationSet_surjective
    {Obs : Type u₂} :
    Function.Surjective
      (empiricalClassToRealizableObservationSet :
        EmpiricalModelQuotient.{u₁, u₂} Obs →
          RealizableObservationSet.{u₁, u₂} Obs) := by
  intro observations
  rcases observations.property with
    ⟨M, hRealized⟩
  refine ⟨empiricalModelClass M, ?_⟩
  apply Subtype.ext
  change
    empiricalReachableObservationSet
        (empiricalModelClass M) =
      observations.1
  calc
    empiricalReachableObservationSet
        (empiricalModelClass M) =
      ReachableObservationSet M :=
        empiricalReachableObservationSet_empiricalModelClass M
    _ = observations.1 :=
      hRealized

/--
The empirical model quotient is equivalent to the type of realizable
reachable-observation sets.
-/
noncomputable def empiricalModelQuotientEquivRealizableObservationSet
    (Obs : Type u₂) :
    EmpiricalModelQuotient.{u₁, u₂} Obs ≃
      RealizableObservationSet.{u₁, u₂} Obs :=
  Equiv.ofBijective
    (empiricalClassToRealizableObservationSet :
      EmpiricalModelQuotient.{u₁, u₂} Obs →
        RealizableObservationSet.{u₁, u₂} Obs)
    ⟨empiricalClassToRealizableObservationSet_injective,
      empiricalClassToRealizableObservationSet_surjective⟩

/--
The canonical equivalence sends the empirical class of a model to its
realizable reachable-observation set.
-/
@[simp]
theorem empiricalModelQuotientEquivRealizableObservationSet_apply
    {Obs : Type u₂}
    (M : GenerativeModel.{u₁, u₂} Obs) :
    ((empiricalModelQuotientEquivRealizableObservationSet Obs)
        (empiricalModelClass M)).1 =
      ReachableObservationSet M := by
  change
    (empiricalClassToRealizableObservationSet
        (empiricalModelClass M)).1 =
      ReachableObservationSet M
  exact
    empiricalClassToRealizableObservationSet_val M

/-!
## Universal descent of empirical measurements

The previous results treated proposition-valued model properties.

The same quotient principle applies to arbitrary measurements. Any
function on generative models that assigns equal values to
observationally equivalent models descends uniquely to the empirical
model quotient.
-/

/--
A model-valued measurement is observation-invariant when
observationally equivalent models always receive the same value.
-/
def ObservationInvariantMap
    {Obs : Type u₂}
    {Value : Type u₃}
    (F : GenerativeModel.{u₁, u₂} Obs → Value) :
    Prop :=
  ∀ M N : GenerativeModel.{u₁, u₂} Obs,
    ModelObsEq M N → F M = F N

/--
Every observation-invariant map descends to a well-defined function
on the empirical model quotient.
-/
def descendInvariantMap
    {Obs : Type u₂}
    {Value : Type u₃}
    (F : GenerativeModel.{u₁, u₂} Obs → Value)
    (hInvariant : ObservationInvariantMap F) :
    EmpiricalModelQuotient.{u₁, u₂} Obs → Value :=
  Quotient.lift F (by
    intro M N hMN
    change ModelObsEq M N at hMN
    exact hInvariant M N hMN)

/--
Evaluating the descended map on the empirical class of a model
returns the original value of the map on that model.
-/
@[simp]
theorem descendInvariantMap_empiricalModelClass
    {Obs : Type u₂}
    {Value : Type u₃}
    (F : GenerativeModel.{u₁, u₂} Obs → Value)
    (hInvariant : ObservationInvariantMap F)
    (M : GenerativeModel.{u₁, u₂} Obs) :
    descendInvariantMap F hInvariant
        (empiricalModelClass M) =
      F M := by
  simp [descendInvariantMap, empiricalModelClass]

/--
The descended map is uniquely determined by its values on empirical
model classes.
-/
theorem descendInvariantMap_unique
    {Obs : Type u₂}
    {Value : Type u₃}
    (F : GenerativeModel.{u₁, u₂} Obs → Value)
    (hInvariant : ObservationInvariantMap F)
    (G : EmpiricalModelQuotient.{u₁, u₂} Obs → Value)
    (hG :
      ∀ M : GenerativeModel.{u₁, u₂} Obs,
        G (empiricalModelClass M) = F M) :
    G = descendInvariantMap F hInvariant := by
  funext empiricalClass
  refine Quotient.inductionOn empiricalClass ?_
  intro M
  change
    G (empiricalModelClass M) =
      descendInvariantMap F hInvariant
        (empiricalModelClass M)
  rw [descendInvariantMap_empiricalModelClass]
  exact hG M

/--
Every observation-invariant map has a unique representation on the
empirical model quotient.
-/
theorem empiricalModelQuotient_map_universal_property
    {Obs : Type u₂}
    {Value : Type u₃}
    (F : GenerativeModel.{u₁, u₂} Obs → Value)
    (hInvariant : ObservationInvariantMap F) :
    ∃! G : EmpiricalModelQuotient.{u₁, u₂} Obs → Value,
      ∀ M : GenerativeModel.{u₁, u₂} Obs,
        G (empiricalModelClass M) = F M := by
  refine ⟨descendInvariantMap F hInvariant, ?_, ?_⟩
  · intro M
    exact
      descendInvariantMap_empiricalModelClass
        F hInvariant M
  · intro G hG
    exact
      descendInvariantMap_unique
        F hInvariant G hG

/-!
## Pullback of empirical measurements

Every function defined on empirical equivalence classes pulls back to
an observation-invariant function on generative models.
-/

/--
A function on empirical classes pulls back to a function on
generative models.
-/
def pullbackEmpiricalMap
    {Obs : Type u₂}
    {Value : Type u₃}
    (G : EmpiricalModelQuotient.{u₁, u₂} Obs → Value) :
    GenerativeModel.{u₁, u₂} Obs → Value :=
  fun M => G (empiricalModelClass M)

/--
Every map pulled back from the empirical quotient is
observation-invariant.
-/
theorem pullbackEmpiricalMap_invariant
    {Obs : Type u₂}
    {Value : Type u₃}
    (G : EmpiricalModelQuotient.{u₁, u₂} Obs → Value) :
    ObservationInvariantMap
      (pullbackEmpiricalMap G) := by
  intro M N hMN
  unfold pullbackEmpiricalMap
  have hClass :
      empiricalModelClass M =
        empiricalModelClass N :=
    (empiricalModelClass_eq_iff_modelObsEq M N).2 hMN
  exact congrArg G hClass

/-!
## Factorization of empirical measurements
-/

/--
A map factors through the empirical quotient when its value depends
only on the empirical equivalence class of the model.
-/
def MapFactorsThroughEmpiricalModelQuotient
    {Obs : Type u₂}
    {Value : Type u₃}
    (F : GenerativeModel.{u₁, u₂} Obs → Value) :
    Prop :=
  ∃ G : EmpiricalModelQuotient.{u₁, u₂} Obs → Value,
    ∀ M : GenerativeModel.{u₁, u₂} Obs,
      F M = G (empiricalModelClass M)

/--
A map is observation-invariant exactly when it factors through the
empirical model quotient.
-/
theorem observationInvariantMap_iff_factorsThroughEmpiricalModelQuotient
    {Obs : Type u₂}
    {Value : Type u₃}
    (F : GenerativeModel.{u₁, u₂} Obs → Value) :
    ObservationInvariantMap F ↔
      MapFactorsThroughEmpiricalModelQuotient F := by
  constructor
  · intro hInvariant
    refine ⟨descendInvariantMap F hInvariant, ?_⟩
    intro M
    exact
      (descendInvariantMap_empiricalModelClass
        F hInvariant M).symm
  · rintro ⟨G, hFactor⟩
    intro M N hMN
    have hClass :
        empiricalModelClass M =
          empiricalModelClass N :=
      (empiricalModelClass_eq_iff_modelObsEq M N).2 hMN
    calc
      F M = G (empiricalModelClass M) :=
        hFactor M
      _ = G (empiricalModelClass N) :=
        congrArg G hClass
      _ = F N :=
        (hFactor N).symm

/-!
## Reachable observations as the canonical empirical measurement

The reachable-observation set is observation-invariant. Its descent
to the empirical quotient is exactly the previously defined
empirical reachable-observation-set map.
-/

/--
The reachable-observation-set map is observation-invariant.
-/
theorem reachableObservationSet_observationInvariantMap
    {Obs : Type u₂} :
    ObservationInvariantMap
      (fun M : GenerativeModel.{u₁, u₂} Obs =>
        ReachableObservationSet M) := by
  intro M N hMN
  exact
    (modelObsEq_iff_reachableObservationSet_eq
      M N).mp hMN

/--
The quotient descent of the reachable-observation-set map equals the
canonical empirical reachable-observation-set function.
-/
theorem descend_reachableObservationSet_eq_empiricalReachableObservationSet
    {Obs : Type u₂} :
    descendInvariantMap
        (fun M : GenerativeModel.{u₁, u₂} Obs =>
          ReachableObservationSet M)
        reachableObservationSet_observationInvariantMap =
      empiricalReachableObservationSet := by
  funext empiricalClass
  refine Quotient.inductionOn empiricalClass ?_
  intro M
  change
    descendInvariantMap
        (fun N : GenerativeModel.{u₁, u₂} Obs =>
          ReachableObservationSet N)
        reachableObservationSet_observationInvariantMap
        (empiricalModelClass M) =
      empiricalReachableObservationSet
        (empiricalModelClass M)
  rw [descendInvariantMap_empiricalModelClass]
  exact
    (empiricalReachableObservationSet_empiricalModelClass
      M).symm

/-!
## Hidden variation within one empirical class

The Boolean extension changes the latent representation without
changing any reachable observation.

Consequently, the original model and its Boolean extension belong to
the same empirical equivalence class, produce the same outcomes under
every admissible experiment, and receive equal values under every
observation-invariant map.
-/

/--
A model is observationally equivalent to its Boolean hidden
extension.
-/
theorem booleanExtension_modelObsEq
    {Obs : Type u₂}
    (M : GenerativeModel.{u₁, u₂} Obs) :
    ModelObsEq M (booleanExtensionModel M) := by
  intro observation
  constructor
  · rintro ⟨state, hState⟩
    refine ⟨(state, false), ?_⟩
    simpa [booleanExtensionModel] using hState
  · rintro ⟨state, hState⟩
    refine ⟨state.1, ?_⟩
    simpa [booleanExtensionModel] using hState

/--
A model and its Boolean hidden extension determine the same empirical
model class.
-/
theorem booleanExtension_same_empiricalModelClass
    {Obs : Type u₂}
    (M : GenerativeModel.{u₁, u₂} Obs) :
    empiricalModelClass M =
      empiricalModelClass (booleanExtensionModel M) := by
  apply
    (empiricalModelClass_eq_iff_modelObsEq
      M
      (booleanExtensionModel M)).2
  exact booleanExtension_modelObsEq M

/--
A model and its Boolean hidden extension have the same reachable
observation set.
-/
theorem booleanExtension_same_reachableObservationSet
    {Obs : Type u₂}
    (M : GenerativeModel.{u₁, u₂} Obs) :
    ReachableObservationSet
        (booleanExtensionModel M) =
      ReachableObservationSet M := by
  apply
    (modelObsEq_iff_reachableObservationSet_eq
      (booleanExtensionModel M)
      M).1
  exact
    modelObsEq_symm
      (booleanExtension_modelObsEq M)

/--
Every admissible experiment has the same possible outcome set on a
model and its Boolean hidden extension.
-/
theorem booleanExtension_same_experimentOutcomeSet
    {Obs : Type u₂}
    {Result : Type u₃}
    (M : GenerativeModel.{u₁, u₂} Obs)
    (experiment : AdmissibleExperiment Obs Result) :
    ExperimentOutcomeSet
        (booleanExtensionModel M)
        experiment =
      ExperimentOutcomeSet M experiment := by
  exact
    modelObsEq_preserves_experimentOutcomeSet
      (booleanExtensionModel M)
      M
      (modelObsEq_symm
        (booleanExtension_modelObsEq M))
      experiment

/--
Every observation-invariant map assigns the same value to a model and
its Boolean hidden extension.
-/
theorem observationInvariantMap_cannot_distinguish_booleanExtension
    {Obs : Type u₂}
    {Value : Type u₃}
    (M : GenerativeModel.{u₁, u₂} Obs)
    (F : GenerativeModel.{u₁, u₂} Obs → Value)
    (hInvariant : ObservationInvariantMap F) :
    F (booleanExtensionModel M) = F M := by
  exact
    hInvariant
      (booleanExtensionModel M)
      M
      (modelObsEq_symm
        (booleanExtension_modelObsEq M))

/-!
## Nondecodable representatives inside empirical classes

Whenever the original model contains a latent state, its empirical
class contains a strict hidden extension whose latent state cannot be
reconstructed exactly from its observation.
-/

/--
Every inhabited model has a nondecodable representative in the same
empirical equivalence class.
-/
theorem inhabited_empiricalClass_contains_nondecodable_model
    {Obs : Type u₂}
    (M : GenerativeModel.{u₁, u₂} Obs)
    (x : M.Latent) :
    ∃ Extended : GenerativeModel.{u₁, u₂} Obs,
      empiricalModelClass Extended =
          empiricalModelClass M ∧
        ¬ HasExactLatentDecoder Extended := by
  let Extended : GenerativeModel.{u₁, u₂} Obs :=
    booleanExtensionModel M
  have hStrict : StrictLatentCover Extended M := by
    exact booleanExtensionStrictCover M x
  refine ⟨Extended, ?_, ?_⟩
  · apply
      (empiricalModelClass_eq_iff_modelObsEq
        Extended M).2
    exact
      modelObsEq_of_strictLatentCover
        Extended M hStrict
  · exact
      strictLatentCover_extended_has_no_exactLatentDecoder
        Extended M hStrict

/--
Every inhabited empirical class contains both the original model and
a strict hidden extension that cannot possess an exact latent
decoder.
-/
theorem inhabited_empiricalClass_contains_strict_hidden_representative
    {Obs : Type u₂}
    (M : GenerativeModel.{u₁, u₂} Obs)
    (x : M.Latent) :
    ∃ Extended : GenerativeModel.{u₁, u₂} Obs,
      Nonempty (StrictLatentCover Extended M) ∧
        empiricalModelClass Extended =
          empiricalModelClass M ∧
        ¬ HasExactLatentDecoder Extended := by
  let Extended : GenerativeModel.{u₁, u₂} Obs :=
    booleanExtensionModel M
  have hStrict : StrictLatentCover Extended M := by
    exact booleanExtensionStrictCover M x
  refine ⟨Extended, ?_⟩
  constructor
  · exact ⟨hStrict⟩
  constructor
  · apply
      (empiricalModelClass_eq_iff_modelObsEq
        Extended M).2
    exact
      modelObsEq_of_strictLatentCover
        Extended M hStrict
  · exact
      strictLatentCover_extended_has_no_exactLatentDecoder
        Extended M hStrict

/-!
## Boundary-limited observer synthesis

For every inhabited model and every admissible experiment, there is a
strict hidden extension that lies in the same empirical class,
produces exactly the same reachable observations and experimental
outcomes, yet does not admit exact latent reconstruction.
-/

/--
An inhabited model always admits a strict empirically
indistinguishable hidden extension whose latent state cannot be
exactly decoded.
-/
theorem boundaryLimitedObserver_synthesis
    {Obs : Type u₂}
    {Result : Type u₃}
    (M : GenerativeModel.{u₁, u₂} Obs)
    (x : M.Latent)
    (experiment : AdmissibleExperiment Obs Result) :
    ∃ Extended : GenerativeModel.{u₁, u₂} Obs,
      Nonempty (StrictLatentCover Extended M) ∧
        empiricalModelClass Extended =
          empiricalModelClass M ∧
        ReachableObservationSet Extended =
          ReachableObservationSet M ∧
        ExperimentOutcomeSet Extended experiment =
          ExperimentOutcomeSet M experiment ∧
        ¬ HasExactLatentDecoder Extended := by
  let Extended : GenerativeModel.{u₁, u₂} Obs :=
    booleanExtensionModel M
  have hStrict : StrictLatentCover Extended M := by
    exact booleanExtensionStrictCover M x
  have hObsEq : ModelObsEq Extended M := by
    exact
      modelObsEq_of_strictLatentCover
        Extended M hStrict
  refine ⟨Extended, ?_⟩
  constructor
  · exact ⟨hStrict⟩
  constructor
  · exact
      (empiricalModelClass_eq_iff_modelObsEq
        Extended M).2 hObsEq
  constructor
  · exact
      (modelObsEq_iff_reachableObservationSet_eq
        Extended M).1 hObsEq
  constructor
  · exact
      modelObsEq_preserves_experimentOutcomeSet
        Extended M hObsEq experiment
  · exact
      strictLatentCover_extended_has_no_exactLatentDecoder
        Extended M hStrict

end BoundaryObserver
