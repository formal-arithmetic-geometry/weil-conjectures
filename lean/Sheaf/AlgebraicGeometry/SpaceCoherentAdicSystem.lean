module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentIdeal
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceArtinRees
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.AlgebraicGeometry.Coherent
public import Sheaf.AlgebraicGeometry.SpaceProperQuotFunctor

/-! # Coherent adic systems on algebraic spaces

Source: Stacks Project, spaces-more-morphisms.tex, Section section-existence-proper,
the definition preceding lemma-inverse-systems-abelian, equation-completion-functor
(Tag 08B4), and remark-inverse-systems-kernel-cokernel-annihilated-by (Tag 08BA)
(blueprint: def-sfb-space-coherent-adic-system).

The index `op n` means level n+1. Morphisms are natural transformations, so their
compatibility, identities and composition are those of the inverse-system category.
The quotient models retain their projections and full universal properties.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- The section family of J^n M, including J^0 M = M. The existing local ideal-product
construction sheafifies membership in finite sums of products of ideal sections.
Source: Stacks, section-existence-proper, ideal powers
(blueprint: def-sfb-space-coherent-adic-system). -/
def adicPowerSections (J : QuasiCoherentIdeal X) (M : X.Modules) (n : ℕ)
    (T : X.EtaleSite) : Set (M.val.obj (op T)) :=
  idealPowerSubsheafSections J.val.arrow M (fun _ ↦ Set.univ) n T

/-- Annihilation by J^n means that every section of the actual locally generated
subsheaf J^n M is zero, rather than just annihilation of global sections.
Source: Stacks, section-existence-proper, condition (1)
(blueprint: def-sfb-space-coherent-adic-system). -/
def AdicPowerKills (J : QuasiCoherentIdeal X) (n : ℕ) (M : X.Modules) : Prop :=
  ∀ (T : X.EtaleSite) (s : M.val.obj (op T)), s ∈ adicPowerSections J M n T → s = 0

/-- A map kills the ideal-product subsheaf when it kills all its local sections.
Source: Stacks, equation-completion-functor, ordinary sheaf quotients
(blueprint: def-sfb-space-coherent-adic-system). -/
def AdicQuotientKills (J : QuasiCoherentIdeal X) (n : ℕ)
    {M N : X.Modules} (f : M ⟶ N) : Prop :=
  ∀ (T : X.EtaleSite) (s : M.val.obj (op T)),
    s ∈ adicPowerSections J M n T → f.val.app (op T) s = 0

/-- The complete quotient construction M ↦ (M/J^(n+1)M)_n. Its projections have the
full cokernel universal property. The two naturality conditions fix both the quotient
transitions and the maps induced by module morphisms.
Source: Stacks, equation-completion-functor (Tag 08B4)
(blueprint: def-sfb-space-coherent-adic-system). -/
structure AdicQuotientModel (J : QuasiCoherentIdeal X) where
  diagram : X.Modules ⥤ (ℕᵒᵖ ⥤ X.Modules)
  projection (M : X.Modules) (n : ℕ) : M ⟶ (diagram.obj M).obj (op n)
  kills (M : X.Modules) (n : ℕ) : AdicQuotientKills J (n + 1) (projection M n)
  universal (M N : X.Modules) (n : ℕ) (f : M ⟶ N) :
    AdicQuotientKills J (n + 1) f →
      ∃! d : (diagram.obj M).obj (op n) ⟶ N, projection M n ≫ d = f
  transition (M : X.Modules) (m n : ℕ) (h : m ≤ n) :
    projection M n ≫ (diagram.obj M).map (homOfLE h).op = projection M m
  naturality {M N : X.Modules} (f : M ⟶ N) (n : ℕ) :
    projection M n ≫ (diagram.map f).app (op n) = f ≫ projection N n

/-- The quotient model exists and is uniquely determined up to its unique
projection-preserving natural isomorphism.
Source: Stacks, equation-completion-functor (Tag 08B4), Modules on Sites, cokernels
(blueprint: def-sfb-space-coherent-adic-system).

Proof: form the subsheaf whose sections are adicPowerSections, using the existing
local-membership construction. Restriction, addition and scalar multiplication preserve
local membership, and the sheaf gluing axiom proves this is a module subsheaf. Take its
ordinary sheaf cokernel. This exists in the original module universe by restriction to
the small affine etale model and its module equivalence. The cokernel property is exactly
the displayed universal factorization. Ideal-power inclusions give unique transition
maps. A module map preserves the local products and hence induces unique quotient maps.
Uniqueness proves the identity, composition and naturality laws. Given two models, factor
each projection through the other. The factorizations are mutually inverse and natural
in both the module and exponent, by the same uniqueness. This also gives uniqueness of
the projection-preserving natural isomorphism. -/
theorem adicQuotientModel_exists (J : QuasiCoherentIdeal X) :
    ∃ P : AdicQuotientModel J, ∀ Q : AdicQuotientModel J,
      ∃! e : P.diagram ≅ Q.diagram,
        ∀ (M : X.Modules) (n : ℕ),
          P.projection M n ≫ (e.app M).hom.app (op n) = Q.projection M n := by
  sorry

/-- The canonical ordinary sheaf quotient model, chosen by its full universal property
and the uniqueness preserving every quotient projection, not by mere existence.
Source: Stacks, equation-completion-functor (Tag 08B4)
(blueprint: def-sfb-space-coherent-adic-system). -/
def adicQuotientModel (J : QuasiCoherentIdeal X) : AdicQuotientModel J :=
  (adicQuotientModel_exists J).choose

/-- Coherence on every level, annihilation by J^(n+1), and the quotient isomorphism
induced by the actual transition. The isomorphism is required to commute with the
canonical quotient projection, so it cannot be an unrelated abstract isomorphism.
Source: Stacks, definition preceding lemma-inverse-systems-abelian
(blueprint: def-sfb-space-coherent-adic-system). -/
def IsCoherentAdicSystem (J : QuasiCoherentIdeal X) :
    ObjectProperty (ℕᵒᵖ ⥤ X.Modules) := fun F ↦
  (∀ n : ℕ, (F.obj (op n)).IsQuasicoherent ∧
    ∀ T : X.EtaleSite, RingedSpace.IsCoherent (X.etaleForget.obj T).toRingedSpace
      ((X.schemeRestriction T).obj (F.obj (op n)))) ∧
  (∀ n : ℕ, AdicPowerKills J (n + 1) (F.obj (op n))) ∧
  (∀ n : ℕ, ∃ e : ((adicQuotientModel J).diagram.obj (F.obj (op (n + 1)))).obj (op n)
      ≅ F.obj (op n),
    (adicQuotientModel J).projection (F.obj (op (n + 1))) n ≫ e.hom =
      F.map (homOfLE (Nat.le_succ n)).op)

/-- Coh(X,J), for a locally Noetherian, quasi-compact, quasi-separated space.
Arrows are precisely compatible families; the inherited category operations are
componentwise. No level zero is imposed on its objects.
Source: Stacks, definition preceding lemma-inverse-systems-abelian
(blueprint: def-sfb-space-coherent-adic-system). -/
abbrev CoherentAdicSystem (X : AlgebraicSpace S) (J : QuasiCoherentIdeal X)
    (_hln : ∀ T : X.EtaleSite, IsLocallyNoetherian (X.etaleForget.obj T))
    (_hqc : CompactSpace (Point X.obj.obj)) (_hqs : IsAbsolutelyQuasiSeparated X) :=
  (IsCoherentAdicSystem J).FullSubcategory

/-- The completion diagram, including its quotient transitions and induced maps on
module morphisms. Restriction to coherent input modules is the completion in the node.
Source: Stacks, equation-completion-functor (Tag 08B4)
(blueprint: def-sfb-space-coherent-adic-system). -/
def coherentAdicCompletionDiagram (J : QuasiCoherentIdeal X) :
    X.Modules ⥤ (ℕᵒᵖ ⥤ X.Modules) :=
  (adicQuotientModel J).diagram

/-- A coherent module gives an object of Coh(X,J).
Source: Stacks, equation-completion-functor (Tag 08B4)
(blueprint: def-sfb-space-coherent-adic-system).

Proof: on every locally Noetherian etale chart a coherent module and its quotients
by ideal powers are coherent. The Zariski/etale quasi-coherent comparison identifies
these with the quotients specified by AdicQuotientModel. They are annihilated by the
respective ideal powers. Since J^(n+2)M is contained in J^(n+1)M, quotienting M/J^(n+2)M
again by J^(n+1) gives M/J^(n+1)M. The universal property identifies the resulting
isomorphism with the actual transition, because both commute with the projection
from M. The chart statements descend, proving each of the three object conditions. -/
theorem coherentAdicCompletionDiagram_isAdic (J : QuasiCoherentIdeal X)
    (hln : ∀ T : X.EtaleSite, IsLocallyNoetherian (X.etaleForget.obj T))
    (M : X.Modules) (hqc : M.IsQuasicoherent)
    (hcoh : ∀ T : X.EtaleSite, RingedSpace.IsCoherent (X.etaleForget.obj T).toRingedSpace
      ((X.schemeRestriction T).obj M)) :
    IsCoherentAdicSystem J ((coherentAdicCompletionDiagram J).obj M) := by
  sorry

/-- The completion functor on coherent modules, with values in Coh(X,J).
Source: Stacks, equation-completion-functor (Tag 08B4)
(blueprint: def-sfb-space-coherent-adic-system). -/
def coherentAdicCompletion (J : QuasiCoherentIdeal X)
    (hln : ∀ T : X.EtaleSite, IsLocallyNoetherian (X.etaleForget.obj T))
    (hqc : CompactSpace (Point X.obj.obj)) (hqs : IsAbsolutelyQuasiSeparated X) :
    ObjectProperty.FullSubcategory (C := X.Modules)
      (fun M ↦ M.IsQuasicoherent ∧ ∀ T : X.EtaleSite,
        RingedSpace.IsCoherent (X.etaleForget.obj T).toRingedSpace
          ((X.schemeRestriction T).obj M)) ⥤ CoherentAdicSystem X J hln hqc hqs :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ coherentAdicCompletionDiagram J)
    (fun M ↦ coherentAdicCompletionDiagram_isAdic J hln M.obj M.property.1 M.property.2)

/-- Termwise tensor pullback of diagrams and their maps. This only asserts a diagram,
without an unstated preservation or exactness hypothesis on g.
Source: Stacks, section-existence-proper, Functoriality
(blueprint: def-sfb-space-coherent-adic-system). -/
def coherentAdicPullbackDiagram (g : X ⟶ Y) :
    (ℕᵒᵖ ⥤ Y.Modules) ⥤ (ℕᵒᵖ ⥤ X.Modules) :=
  (Functor.whiskeringRight ℕᵒᵖ Y.Modules X.Modules).obj (moduleTensorPullback g)

/-- Proper support of a system is the proper closed-carrier condition on level one.
For this relative clause the base is Spec A and f is its separated finite-type
structural map. The carrier convention is exactly the proper-support Quot convention.
Source: Stacks, paragraph preceding equation-completion-functor-proper-over-A
(blueprint: def-sfb-space-coherent-adic-system). -/
def CoherentAdicHasProperSupport {A : Type u} [CommRing A]
    {X : AlgebraicSpace (Spec (.of A))}
    (f : X ⟶ schemeSpace (Over.mk (𝟙 (Spec (.of A))))) (_hsep : MapIsSeparated f)
    (_hft : MapIsFiniteType f) (F : ℕᵒᵖ ⥤ X.Modules) : Prop :=
  ∃ (Z : AlgebraicSpace (Spec (.of A))) (i : Z ⟶ X),
    IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) i.hom.hom ∧
    MapIsProper (i ≫ f) ∧ ∃ Q : Z.Modules,
      Q.IsQuasicoherent ∧ Q.IsFiniteType ∧
        Nonempty ((moduleDirectImage i).obj Q ≅ F.obj (op 0))

/-- One common positive exponent kills every ordinary component kernel and cokernel.
Their universal properties are in all module sheaves, not in the adic category.
Quantifying over these universal properties avoids any alternative cokernel construction.
Source: Stacks, Tag 08BA, condition (1)
(blueprint: def-sfb-space-coherent-adic-system). -/
def CoherentAdicKernelCokernelKilled (K : QuasiCoherentIdeal X)
    {F G : ℕᵒᵖ ⥤ X.Modules} (a : F ⟶ G) : Prop :=
  ∃ t : ℕ, 1 ≤ t ∧ ∀ n : ℕ,
    (∀ k : KernelFork (a.app (op n)), IsLimit k → AdicPowerKills K t k.pt) ∧
    (∀ c : CokernelCofork (a.app (op n)), IsColimit c → AdicPowerKills K t c.pt)

/-- The closed-carrier convention for proper support, with an arbitrary structural map.
This is the same carrier condition used by CoherentAdicHasProperSupport, before taking
level one, and uses the specified module direct image.
Source: Stacks, Situation 08B7, paragraph before equation-completion-functor-proper-over-A
(blueprint: def-sfb-space-coherent-adic-system). -/
def ModuleHasProperClosedCarrier {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (M : X.Modules) : Prop :=
  ∃ (Z : AlgebraicSpace S) (i : Z ⟶ X),
    IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) i.hom.hom ∧
    MapIsProper (i ≫ f) ∧ ∃ Q : Z.Modules,
      Q.IsQuasicoherent ∧ Q.IsFiniteType ∧ Nonempty ((moduleDirectImage i).obj Q ≅ M)

/-- Coherent modules with proper support, as a full subcategory of the given module site.
Coherence uses exactly the recorded quasi-coherence and coherent chart restrictions.
Source: Stacks, Situation 08B7, paragraph before equation-completion-functor-proper-over-A
(blueprint: def-sfb-space-coherent-adic-system). -/
abbrev CoherentProperSupportModules {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :=
  ObjectProperty.FullSubcategory (C := X.Modules) (fun M ↦
    M.IsQuasicoherent ∧
      (∀ T : X.EtaleSite, RingedSpace.IsCoherent (X.etaleForget.obj T).toRingedSpace
        ((X.schemeRestriction T).obj M)) ∧ ModuleHasProperClosedCarrier f M)

/-- Proper support of an adic diagram means proper support of its first positive term.
The index op n denotes level n+1; no artificial level zero condition is imposed.
Source: Stacks, Situation 08B7, paragraph before equation-completion-functor-proper-over-A
(blueprint: def-sfb-space-coherent-adic-system). -/
def CoherentAdicHasProperSupportOver {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (M : ℕᵒᵖ ⥤ X.Modules) : Prop :=
  ModuleHasProperClosedCarrier f (M.obj (op 0))

end AlgebraicGeometry.AlgebraicSpace
