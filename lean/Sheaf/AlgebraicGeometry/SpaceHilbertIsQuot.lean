module

public import Sheaf.AlgebraicGeometry.SpaceProperHilbertFunctor
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleStructureMap
public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Sheaf.AlgebraicGeometry.AlgebraicSpaceClosedIdealCorrespondence
import Sheaf.AlgebraicGeometry.AlgebraicSpaceClosedStructureFinitePresentation
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperFpLocality

/-! # The proper Hilbert presheaf is the Quot presheaf of the structure sheaf

Source: Stacks Project, quot.tex, Tag 0D00, lemma-hilb-is-quot
(blueprint: lem-sfb-space-hilbert-is-quot).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {A B : AlgebraicSpace S}

/-- The structure module is quasi-coherent on the small etale site.
Source: Stacks, Tag 0D00, with Modules on Sites, Tag 03DL
(blueprint: lem-sfb-space-hilbert-is-quot).
Proof: on every etale scheme chart the structure module has the presentation with one
generator, no relations, and identity augmentation. These presentations are compatible
with restriction, and cover the site. They give QuasicoherentData for the unit module.
This is the implicit quasi-coherence required to form Quot of O_A in the node. -/
theorem hilbertStructureModule_quasicoherent (A : AlgebraicSpace S) :
    (SheafOfModules.unit A.structureSheaf).IsQuasicoherent := by
  sorry

/-- The quasi-coherent structure module, using the existing unit module.
Source: Stacks, Tag 0D00 (blueprint: lem-sfb-space-hilbert-is-quot). -/
def hilbertStructureModule (A : AlgebraicSpace S) : A.QCoh :=
  ⟨SheafOfModules.unit A.structureSheaf, hilbertStructureModule_quasicoherent A⟩

/-- The canonical identification of Hilbert objects with structure-sheaf quotients.
The first equation normalizes pullback of O_A by its adjunction. The forward equation
specifies the actual structure quotient, up to exactly the target isomorphisms used by
Quot. The last equation identifies the inverse closed subspace by its kernel ideal.
The natural isomorphism includes both directions of naturality for every test morphism.
Source: Stacks Project, quot.tex, Tag 0D00, lemma-hilb-is-quot
(blueprint: lem-sfb-space-hilbert-is-quot).

Proof:
1. For T, put X = A_T. Finite presentation of a persists by base change, by
lem-sfb-space-flat-proper-fp-locality. For a Hilbert family D, relative local finite
presentation permanence (lem-sfb-space-relative-lfp-permanence) makes its inclusion
locally finitely presented. The closed-structure criterion
lem-sfb-space-closed-structure-finite-presentation gives finite presentation of i_*O_D.
2. By lem-sfb-space-closed-immersion-quasi-coherent-modules, the structure map is
surjective with quasi-coherent target. By lem-sfb-space-closed-pushforward-relative-flatness
its target is flat over T. The carrier D, with its finite type module O_D, supplies the
proper support in def-sfb-space-proper-quot-functor. Isomorphic closed immersions give
intertwining target isomorphisms, so the forward assignment descends to classes.
3. Conversely, the kernel of a quotient is quasi-coherent by
lem-sfb-space-qcoh-kernels-colimits and is an ideal by O_X-linearity. By
lem-sfb-space-closed-ideal-correspondence it defines a unique closed-subspace class D,
and the quotient identifies with i_*O_D compatibly with the structure map. The closed
structure criterion and lem-sfb-space-separated-fp-composition make D → T finitely
presented.
4. Relative flatness follows from lem-sfb-space-closed-pushforward-relative-flatness.
Since X → T is locally of finite type, lem-sfb-space-module-proper-carrier-support makes
D → T proper from the proper-carrier condition on the quotient. No Noetherian hypothesis
is used.
5. Intertwining target isomorphisms give equal kernels. The closed-ideal correspondence
therefore proves that the constructions are mutually inverse on exactly the specified
isomorphism classes.
6. For any T' → T, lem-sfb-space-closed-ideal-correspondence identifies the pulled
structure quotient with the structure quotient of D ×_T T', preserving the quotient
arrow and its unit normalization. Thus the forward bijections commute with all
transitions; their inverses commute as well by bijectivity. The new ideal is the image
of the pulled ideal; no left exactness or flatness of T' → T is assumed. -/
theorem properHilbert_is_quot (a : A ⟶ B) (ha : ProperQuotFinitePresentation a) :
    ∃ unitIso : ∀ T : ProperQuotTest B,
        (moduleTensorPullback (properQuotFst a T)).obj
            (SheafOfModules.unit A.structureSheaf) ≅
          SheafOfModules.unit (properQuotFibre a T).structureSheaf,
      (∀ T : ProperQuotTest B, (unitIso T).hom =
        ((moduleTensorAdjunction (properQuotFst a T)).homEquiv _ _).symm
          (moduleStructureMap (properQuotFst a T))) ∧
      ∃ e : properHilbertFunctor a ≅ properQuotFunctor a ha (hilbertStructureModule A),
        (∀ (T : ProperQuotTest B) (C : ProperHilbertFamily a T),
          ∃ q : ProperQuotient a (SheafOfModules.unit A.structureSheaf) T,
            e.hom.app (op T) C = Quot.mk _ q ∧
            ∃ θ : q.target ≅ (moduleDirectImage C.val.val.arrow).obj
                (SheafOfModules.unit (C.val.val : AlgebraicSpace S).structureSheaf),
              q.quotient ≫ θ.hom = (unitIso T).hom ≫
                moduleStructureMap C.val.val.arrow) ∧
        (∀ (T : ProperQuotTest B)
            (q : ProperQuotient a (SheafOfModules.unit A.structureSheaf) T),
          kernelSubobject ((unitIso T).inv ≫ q.quotient) =
            kernelSubobject (moduleStructureMap
              (e.inv.app (op T) (Quot.mk _ q)).val.val.arrow)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
