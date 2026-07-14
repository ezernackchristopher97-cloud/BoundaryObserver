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
end BoundaryObserver
