module

public import Sheaf.Paper.NormalizedDVRTower

public import Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness

public import Sheaf.SixFunctors.IntegralCompactificationSystemRealization
public import Sheaf.Paper.SixFunctorOperationDatum
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.Paper.ExchangeProjectionSuppliedDomains
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients

public import Sheaf.SixFunctors.IntegralSystemOperations
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.SfRationalizationKaroubi

/-! # Expressions and maps for the completed projection/base-change diamond

Source: blueprint fix-prop-coherence and fix-prop-projection-formula, projection diamond;
Stacks 0GL1 and 0E48 (blueprint: lem-sf-completed-projection-exchange-realization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOfSpec false
set_option genInjectivity false
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.IntegralSystemRealization
namespace WeilConjectures.CompletedProjectionExchange

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {D : FiniteFieldDatum.{u}} (o : Operations l E) (ρ : Realizations l E D o)
  (Q : SixFunctorCompactifiedSquare D)

/-- The actual open/proper compact-support system functor.
Source: blueprint projection diamond, Stacks 0GL1/0E48
(blueprint: lem-sf-completed-projection-exchange-realization). -/
abbrev support := Operations.shriek l E o Q.compactification.i ⋙
  Operations.push l E o Q.compactification.g

/-- The specified chosen-compactification system exchange.
Source: blueprint projection diamond, Stacks 0GL1/0E48
(blueprint: lem-sf-completed-projection-exchange-realization). -/
def exchange := compactificationExchange l E o ρ.compositors ρ.openComparisons
  Q.compactification Q.compactification' Q.g'.hom.left Q.g.hom.left Q.h.hom.left
  Q.openSquare.w Q.properSquare.w Q.openSquare

/-- The target tensor/pullback identification, including the inverse square comparison.
Source: blueprint projection diamond, Stacks 0GL1/0E48
(blueprint: lem-sf-completed-projection-exchange-realization). -/
def target (M : System l E Q.X.obj.left) (N : System l E Q.Y.obj.left) :=
  (pullbackTensorSystemComparison l E Q.g'.hom.left).hom.app
      (M, (pull l E Q.f.hom.left).obj N) ≫
    (calculus l E Q.X'.obj.left).systemClosed.tensor.map
      (Prod.mkHom (𝟙 _) ((ρ.compositors.square l E Q.g'.hom.left Q.f'.hom.left
        Q.f.hom.left Q.g.hom.left Q.square.w).inv.app N))

/-- Project first, then exchange, then identify the target tensor factors.
Source: blueprint projection diamond, Stacks 0GL1/0E48
(blueprint: lem-sf-completed-projection-exchange-realization). -/
def diamondLeft (M : System l E Q.X.obj.left) (N : System l E Q.Y.obj.left) :=
  (pull l E Q.g.hom.left).map
      (compactificationProjection l E o ρ.compositors ρ.openComparisons Q.compactification M N) ≫
    (exchange l E o ρ Q).app
      ((calculus l E Q.X.obj.left).systemClosed.tensor.obj
        (M, (pull l E Q.f.hom.left).obj N)) ≫
    (Operations.shriek l E o Q.compactification'.i ⋙
      Operations.push l E o Q.compactification'.g).map (target l E o ρ Q M N)

/-- Exchange first, then project; the source pullback/tensor identification is explicit.
Source: blueprint projection diamond, Stacks 0GL1/0E48
(blueprint: lem-sf-completed-projection-exchange-realization). -/
def diamondRight (M : System l E Q.X.obj.left) (N : System l E Q.Y.obj.left) :=
  (pullbackTensorSystemComparison l E Q.g.hom.left).hom.app
      ((support l E o Q).obj M, N) ≫
    (calculus l E Q.Y'.obj.left).systemClosed.tensor.map
      (Prod.mkHom ((exchange l E o ρ Q).app M) (𝟙 _)) ≫
    compactificationProjection l E o ρ.compositors ρ.openComparisons Q.compactification'
      ((pull l E Q.g'.hom.left).obj M) ((pull l E Q.g.hom.left).obj N)

/-- Proper-factor route: projection, exchange, then the tensor/square identification.
Source: blueprint projection diamond, Stacks 0GL1/0E48
(blueprint: lem-sf-completed-projection-exchange-realization). -/
def properFirst (M : System l E Q.Z.obj.left) (N : System l E Q.Y.obj.left) :=
  (pull l E Q.g.hom.left).map (((properProjection l E o Q.p.hom.left).app M).app N) ≫
    (properExchange l E o ρ.compositors Q.h.hom.left Q.p'.hom.left Q.p.hom.left
      Q.g.hom.left Q.properSquare.w).app
      ((calculus l E Q.Z.obj.left).systemClosed.tensor.obj
        (M, (pull l E Q.p.hom.left).obj N)) ≫
    (Operations.push l E o Q.p'.hom.left).map
      ((pullbackTensorSystemComparison l E Q.h.hom.left).hom.app
          (M, (pull l E Q.p.hom.left).obj N) ≫
        (calculus l E Q.Z'.obj.left).systemClosed.tensor.map
          (Prod.mkHom (𝟙 _) ((ρ.compositors.square l E Q.h.hom.left Q.p'.hom.left
            Q.p.hom.left Q.g.hom.left Q.properSquare.w).inv.app N)))

/-- Proper-factor route: pullback tensor, exchange tensor identity, then projection.
Source: blueprint projection diamond, Stacks 0GL1/0E48
(blueprint: lem-sf-completed-projection-exchange-realization). -/
def properSecond (M : System l E Q.Z.obj.left) (N : System l E Q.Y.obj.left) :=
  (pullbackTensorSystemComparison l E Q.g.hom.left).hom.app
      ((Operations.push l E o Q.p.hom.left).obj M, N) ≫
    (calculus l E Q.Y'.obj.left).systemClosed.tensor.map
      (Prod.mkHom ((properExchange l E o ρ.compositors Q.h.hom.left Q.p'.hom.left
        Q.p.hom.left Q.g.hom.left Q.properSquare.w).app M) (𝟙 _)) ≫
    ((properProjection l E o Q.p'.hom.left).app
      ((pull l E Q.h.hom.left).obj M)).app ((pull l E Q.g.hom.left).obj N)

/-- The common proper transpose: canonical identifications followed by H epsilon tensor 1.
Source: blueprint projection diamond, Stacks 0GL1/0E48
(blueprint: lem-sf-completed-projection-exchange-realization). -/
def commonTranspose (M : System l E Q.Z.obj.left) (N : System l E Q.Y.obj.left) :=
  (ρ.compositors.square l E Q.h.hom.left Q.p'.hom.left Q.p.hom.left
      Q.g.hom.left Q.properSquare.w).hom.app
        ((calculus l E Q.Y.obj.left).systemClosed.tensor.obj
          ((Operations.push l E o Q.p.hom.left).obj M, N)) ≫
    (pull l E Q.h.hom.left).map
      ((pullbackTensorSystemComparison l E Q.p.hom.left).hom.app
        ((Operations.push l E o Q.p.hom.left).obj M, N)) ≫
    (pullbackTensorSystemComparison l E Q.h.hom.left).hom.app
      ((pull l E Q.p.hom.left).obj ((Operations.push l E o Q.p.hom.left).obj M),
        (pull l E Q.p.hom.left).obj N) ≫
    (calculus l E Q.Z'.obj.left).systemClosed.tensor.map
      (Prod.mkHom ((pull l E Q.h.hom.left).map ((o.direct Q.p.hom.left).adj.counit.app M))
        ((ρ.compositors.square l E Q.h.hom.left Q.p'.hom.left Q.p.hom.left
          Q.g.hom.left Q.properSquare.w).inv.app N))

/-- The open-factor first route: H gamma, beta, then the tensor/square comparison.
Source: blueprint projection diamond, Stacks 0GL1/0E48
(blueprint: lem-sf-completed-projection-exchange-realization). -/
def openFirst (M : System l E Q.X.obj.left) (P : System l E Q.Z.obj.left) :=
  (pull l E Q.h.hom.left).map
      ((ρ.openComparisons.projection Q.compactification.i).hom.app (M, P)) ≫
    (ρ.openComparisons.beta Q.g'.hom.left Q.compactification'.i Q.compactification.i
      Q.h.hom.left Q.openSquare.w Q.openSquare).hom.app
      ((calculus l E Q.X.obj.left).systemClosed.tensor.obj
        (M, (pull l E Q.compactification.i).obj P)) ≫
    (Operations.shriek l E o Q.compactification'.i).map
      ((pullbackTensorSystemComparison l E Q.g'.hom.left).hom.app
          (M, (pull l E Q.compactification.i).obj P) ≫
        (calculus l E Q.X'.obj.left).systemClosed.tensor.map
          (Prod.mkHom (𝟙 _) ((ρ.compositors.square l E Q.g'.hom.left Q.compactification'.i
            Q.compactification.i Q.h.hom.left Q.openSquare.w).inv.app P)))

/-- The open-factor second route: tensor pullback, beta tensor identity, then gamma prime.
Source: blueprint projection diamond, Stacks 0GL1/0E48
(blueprint: lem-sf-completed-projection-exchange-realization). -/
def openSecond (M : System l E Q.X.obj.left) (P : System l E Q.Z.obj.left) :=
  (pullbackTensorSystemComparison l E Q.h.hom.left).hom.app
      ((Operations.shriek l E o Q.compactification.i).obj M, P) ≫
    (calculus l E Q.Z'.obj.left).systemClosed.tensor.map
      (Prod.mkHom ((ρ.openComparisons.beta Q.g'.hom.left Q.compactification'.i
        Q.compactification.i Q.h.hom.left Q.openSquare.w Q.openSquare).hom.app M) (𝟙 _)) ≫
    (ρ.openComparisons.projection Q.compactification'.i).hom.app
      ((pull l E Q.g'.hom.left).obj M, (pull l E Q.h.hom.left).obj P)

/-- The independently specified unit-normalized identification of the open source.
Source: blueprint projection diamond, Stacks 0GL1/0E48
(blueprint: lem-sf-completed-projection-exchange-realization). -/
def openSource (M : System l E Q.X.obj.left) (P : System l E Q.Z.obj.left) :=
  (ρ.compositors.square l E Q.g'.hom.left Q.compactification'.i Q.compactification.i
      Q.h.hom.left Q.openSquare.w).hom.app
      ((calculus l E Q.Z.obj.left).systemClosed.tensor.obj
        ((Operations.shriek l E o Q.compactification.i).obj M, P)) ≫
    (pull l E Q.g'.hom.left).map
      ((pullbackTensorSystemComparison l E Q.compactification.i).hom.app
        ((Operations.shriek l E o Q.compactification.i).obj M, P)) ≫
    (pullbackTensorSystemComparison l E Q.g'.hom.left).hom.app
      ((pull l E Q.compactification.i).obj
        ((Operations.shriek l E o Q.compactification.i).obj M),
        (pull l E Q.compactification.i).obj P) ≫
    (calculus l E Q.X'.obj.left).systemClosed.tensor.map
      (Prod.mkHom ((pull l E Q.g'.hom.left).map
        ((ρ.openComparisons.unit l E o ρ.compositors Q.compactification.i).inv.app M))
        ((ρ.compositors.square l E Q.g'.hom.left Q.compactification'.i Q.compactification.i
          Q.h.hom.left Q.openSquare.w).inv.app P))

/-- The two input schemes; the universe lift retains arbitrary scheme universes.
Source: blueprint projection diamond, Stacks 0GL1/0E48
(blueprint: lem-sf-completed-projection-exchange-realization). -/
def spaces : ULift.{u} Bool → Over (Spec (CommRingCat.of D.k))
  | ⟨false⟩ => Q.X.obj
  | ⟨true⟩ => Q.Y.obj

/-- The four vertices, as actual finite expression trees, including hidden open intermediates.
Source: blueprint projection diamond, Stacks 0GL1/0E48
(blueprint: lem-sf-completed-projection-exchange-realization). -/
def word : Fin 4 → Expression (Spec (CommRingCat.of D.k)) (ULift.{u} Bool) (spaces Q) Q.Y'.obj
  | 0 => .pull Q.g.hom (.tensor
      (.compactSupport Q.f.hom Q.compactification
        (.var (X := spaces Q) (ULift.up false)))
      (.var (X := spaces Q) (ULift.up true)))
  | 1 => .pull Q.g.hom (.compactSupport Q.f.hom Q.compactification
      (.tensor (.var (X := spaces Q) (ULift.up false))
        (.pull Q.f.hom (.var (X := spaces Q) (ULift.up true)))))
  | 2 => .tensor (.compactSupport Q.f'.hom Q.compactification'
      (.pull Q.g'.hom (.var (X := spaces Q) (ULift.up false))))
      (.pull Q.g.hom (.var (X := spaces Q) (ULift.up true)))
  | 3 => .compactSupport Q.f'.hom Q.compactification'
      (.tensor (.pull Q.g'.hom (.var (X := spaces Q) (ULift.up false)))
        (.pull Q.f'.hom (.pull Q.g.hom (.var (X := spaces Q) (ULift.up true)))))

/-- The original integral inputs, without any finite-Tor hypothesis on the first.
Source: blueprint projection diamond, Stacks 0GL1/0E48
(blueprint: lem-sf-completed-projection-exchange-realization). -/
def inputs (K : Integral l E Q.X.obj.left) (L : Integral l E Q.Y.obj.left) :
    ∀ i : ULift.{u} Bool, Integral l E ((spaces Q) i).left
  | ⟨false⟩ => K
  | ⟨true⟩ => L


/-- Realize the top system route using precisely c_source inverse and c_target.
These are the normalized natural comparisons of the recorded realization theorem.
Source: blueprint projection diamond, proof step 11
(blueprint: lem-sf-completed-projection-exchange-realization). -/
def integralLeft (K : Integral l E Q.X.obj.left) (L : Integral l E Q.Y.obj.left)
    (g₀ : (word Q 0).geometric) (g₃ : (word Q 3).geometric)
    (h₀ : (word Q 0).domain l E o (inputs l E Q K L))
    (h₃ : (word Q 3).domain l E o (inputs l E Q K L)) :=
  (ρ.comparison (word Q 0) g₀).inv.app ⟨inputs l E Q K L, h₀⟩ ≫
    (coefficientSequenceLimit l E Q.Y'.obj.left).map
      (diamondLeft l E o ρ Q ((calculus l E Q.X.obj.left).reduction.obj K)
        ((calculus l E Q.Y.obj.left).reduction.obj L)) ≫
    (ρ.comparison (word Q 3) g₃).hom.app ⟨inputs l E Q K L, h₃⟩

/-- Realize the bottom route by the same two normalized endpoint comparisons.
Source: blueprint projection diamond, proof step 11
(blueprint: lem-sf-completed-projection-exchange-realization). -/
def integralRight (K : Integral l E Q.X.obj.left) (L : Integral l E Q.Y.obj.left)
    (g₀ : (word Q 0).geometric) (g₃ : (word Q 3).geometric)
    (h₀ : (word Q 0).domain l E o (inputs l E Q K L))
    (h₃ : (word Q 3).domain l E o (inputs l E Q K L)) :=
  (ρ.comparison (word Q 0) g₀).inv.app ⟨inputs l E Q K L, h₀⟩ ≫
    (coefficientSequenceLimit l E Q.Y'.obj.left).map
      (diamondRight l E o ρ Q ((calculus l E Q.X.obj.left).reduction.obj K)
        ((calculus l E Q.Y.obj.left).reduction.obj L)) ≫
    (ρ.comparison (word Q 3) g₃).hom.app ⟨inputs l E Q K L, h₃⟩

/-- The complete integral source word G(f!K tensor L).
Source: blueprint projection diamond, first vertex
(blueprint: lem-sf-completed-projection-exchange-realization). -/
abbrev integralSource (K : Integral l E Q.X.obj.left) (L : Integral l E Q.Y.obj.left) :=
  ((word Q 0).evaluate (integralInterpretation l E)).obj (inputs l E Q K L)

/-- The complete integral target word f! prime (g prime star K tensor f prime star g star L).
Source: blueprint projection diamond, fourth vertex
(blueprint: lem-sf-completed-projection-exchange-realization). -/
abbrev integralTarget (K : Integral l E Q.X.obj.left) (L : Integral l E Q.Y.obj.left) :=
  ((word Q 3).evaluate (integralInterpretation l E)).obj (inputs l E Q K L)

/-- Raw localization of the actual realized top route. The endpoint proofs only form
objects of the already specified full subcategory; the main theorem proves them.
Source: blueprint projection diamond, raw-localization paragraph
(blueprint: lem-sf-completed-projection-exchange-realization). -/
def rationalLeft (K : Integral l E Q.X.obj.left) (L : Integral l E Q.Y.obj.left)
    (g₀ : (word Q 0).geometric) (g₃ : (word Q 3).geometric)
    (h₀ : (word Q 0).domain l E o (inputs l E Q K L))
    (h₃ : (word Q 3).domain l E o (inputs l E Q K L))
    (hs : sfIntegralConstructible l E Q.Y'.obj.left (integralSource l E Q K L))
    (ht : sfIntegralConstructible l E Q.Y'.obj.left (integralTarget l E Q K L)) :=
  (sfRationalConstructibleLocalization l E Q.Y'.obj.left).map
    (ObjectProperty.homMk (integralLeft l E o ρ Q K L g₀ g₃ h₀ h₃) :
      (⟨integralSource l E Q K L, hs⟩ : sfIntegralConstructibleCategory l E Q.Y'.obj.left) ⟶
        ⟨integralTarget l E Q K L, ht⟩)

/-- Raw localization of the bottom route using the same endpoint objects.
Source: blueprint projection diamond, raw-localization paragraph
(blueprint: lem-sf-completed-projection-exchange-realization). -/
def rationalRight (K : Integral l E Q.X.obj.left) (L : Integral l E Q.Y.obj.left)
    (g₀ : (word Q 0).geometric) (g₃ : (word Q 3).geometric)
    (h₀ : (word Q 0).domain l E o (inputs l E Q K L))
    (h₃ : (word Q 3).domain l E o (inputs l E Q K L))
    (hs : sfIntegralConstructible l E Q.Y'.obj.left (integralSource l E Q K L))
    (ht : sfIntegralConstructible l E Q.Y'.obj.left (integralTarget l E Q K L)) :=
  (sfRationalConstructibleLocalization l E Q.Y'.obj.left).map
    (ObjectProperty.homMk (integralRight l E o ρ Q K L g₀ g₃ h₀ h₃) :
      (⟨integralSource l E Q K L, hs⟩ : sfIntegralConstructibleCategory l E Q.Y'.obj.left) ⟶
        ⟨integralTarget l E Q K L, ht⟩)

/-- Both open-factor restrictions equal the independently specified open-unit map.
Source: blueprint projection diamond, proof step 8
(blueprint: lem-sf-completed-projection-exchange-realization). -/
def OpenLaw (M : System l E Q.X.obj.left) (P : System l E Q.Z.obj.left) : Prop :=
  (pull l E Q.compactification'.i).map (openFirst l E o ρ Q M P) ≫
      (ρ.openComparisons.unit l E o ρ.compositors Q.compactification'.i).inv.app _ =
    openSource l E o ρ Q M P ∧
  (pull l E Q.compactification'.i).map (openSecond l E o ρ Q M P) ≫
      (ρ.openComparisons.unit l E o ρ.compositors Q.compactification'.i).inv.app _ =
    openSource l E o ρ Q M P

/-- Both proper-factor transposes are the fixed H epsilon tensor identity map.
Source: blueprint projection diamond, proof step 9
(blueprint: lem-sf-completed-projection-exchange-realization). -/
def ProperLaw (M : System l E Q.Z.obj.left) (N : System l E Q.Y.obj.left) : Prop :=
  ((o.direct Q.p'.hom.left).adj.homEquiv _ _).symm
      (properFirst l E o ρ Q M N) = commonTranspose l E o ρ Q M N ∧
  ((o.direct Q.p'.hom.left).adj.homEquiv _ _).symm
      (properSecond l E o ρ Q M N) = commonTranspose l E o ρ Q M N

/-- The complete conclusion of the completed diamond: the four domains, intrinsic
system equality, open restrictions, proper transposes, completed and rational equality,
and canonical realization in arbitrary outer expression contexts. This is only a
transparent conjunction of the displayed assertions.
Source: blueprint projection diamond, all clauses
(blueprint: lem-sf-completed-projection-exchange-realization). -/
def Statement (K : Integral l E Q.X.obj.left) (L : Integral l E Q.Y.obj.left) : Prop :=
    (∀ i : Fin 4, (word Q i).geometric ∧
      (word Q i).domain l E o (inputs l E Q K L)) ∧
    diamondLeft l E o ρ Q ((calculus l E Q.X.obj.left).reduction.obj K)
        ((calculus l E Q.Y.obj.left).reduction.obj L) =
      diamondRight l E o ρ Q ((calculus l E Q.X.obj.left).reduction.obj K)
        ((calculus l E Q.Y.obj.left).reduction.obj L) ∧
    OpenLaw l E o ρ Q ((calculus l E Q.X.obj.left).reduction.obj K)
      ((pull l E Q.p.hom.left).obj ((calculus l E Q.Y.obj.left).reduction.obj L)) ∧
    ProperLaw l E o ρ Q ((Operations.shriek l E o Q.compactification.i).obj
      ((calculus l E Q.X.obj.left).reduction.obj K))
      ((calculus l E Q.Y.obj.left).reduction.obj L) ∧
    (sfIntegralConstructible l E Q.Y'.obj.left (integralSource l E Q K L) ∧
      sfIntegralConstructible l E Q.Y'.obj.left (integralTarget l E Q K L)) ∧
    (∀ (g₀ : (word Q 0).geometric) (g₃ : (word Q 3).geometric)
      (h₀ : (word Q 0).domain l E o (inputs l E Q K L))
      (h₃ : (word Q 3).domain l E o (inputs l E Q K L)),
      CanonicalPair l E o ρ.compositors ρ.openComparisons ρ.canonicalBridge ρ.properOpen
        ρ.ringedModels ρ.ringedOpenComparisons ρ.ringedProperOpen
        ((inputReduction l E (spaces Q)).obj (inputs l E Q K L))
        (inputs l E Q K L) (word Q 0) (word Q 3)
        (diamondLeft l E o ρ Q ((calculus l E Q.X.obj.left).reduction.obj K)
          ((calculus l E Q.Y.obj.left).reduction.obj L))
        (integralLeft l E o ρ Q K L g₀ g₃ h₀ h₃) ∧
      CanonicalPair l E o ρ.compositors ρ.openComparisons ρ.canonicalBridge ρ.properOpen
        ρ.ringedModels ρ.ringedOpenComparisons ρ.ringedProperOpen
        ((inputReduction l E (spaces Q)).obj (inputs l E Q K L))
        (inputs l E Q K L) (word Q 0) (word Q 3)
        (diamondRight l E o ρ Q ((calculus l E Q.X.obj.left).reduction.obj K)
          ((calculus l E Q.Y.obj.left).reduction.obj L))
        (integralRight l E o ρ Q K L g₀ g₃ h₀ h₃) ∧
      integralLeft l E o ρ Q K L g₀ g₃ h₀ h₃ =
        integralRight l E o ρ Q K L g₀ g₃ h₀ h₃ ∧
      ∀ (hs : sfIntegralConstructible l E Q.Y'.obj.left (integralSource l E Q K L))
        (ht : sfIntegralConstructible l E Q.Y'.obj.left (integralTarget l E Q K L)),
        rationalLeft l E o ρ Q K L g₀ g₃ h₀ h₃ hs ht =
          rationalRight l E o ρ Q K L g₀ g₃ h₀ h₃ hs ht) ∧
    (∀ {I : Type u} [Finite I] {X : I → Over (Spec (CommRingCat.of D.k))}
      {W : Over (Spec (CommRingCat.of D.k))} (e t : Expression _ I X W)
      (ge : e.geometric) (gt : t.geometric)
      (A : (e.domain l E o).FullSubcategory) (ht : t.domain l E o A.obj)
      (s : e.systemObj l E o ((inputReduction l E X).obj A.obj) ⟶
        t.systemObj l E o ((inputReduction l E X).obj A.obj))
      (r : (e.evaluate (integralInterpretation l E)).obj A.obj ⟶
        (t.evaluate (integralInterpretation l E)).obj A.obj),
      CanonicalPair l E o ρ.compositors ρ.openComparisons ρ.canonicalBridge ρ.properOpen
        ρ.ringedModels ρ.ringedOpenComparisons ρ.ringedProperOpen
        ((inputReduction l E X).obj A.obj) A.obj e t s r →
      (coefficientSequenceLimit l E W.left).map s ≫
        (ρ.comparison t gt).hom.app ⟨A.obj, ht⟩ = (ρ.comparison e ge).hom.app A ≫ r)

end WeilConjectures.CompletedProjectionExchange
