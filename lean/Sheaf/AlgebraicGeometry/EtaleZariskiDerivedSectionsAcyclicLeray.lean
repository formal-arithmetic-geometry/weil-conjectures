module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Sites.Pullback

import Sheaf.Paper.ZariskiEtaleSheafLeftExact
import Sheaf.CategoryTheory.SitePullbackAbelianUnderlying
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Sheaf.Algebra.Homology.LiftToInjectiveUniqueUpToHomotopy

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

set_option autoImplicit false

/-- Acyclic Leray for right-derived terminal sections, without either Ext model.
Source: Stacks Project, Tags 072Z and 0733(1).
(blueprint: new-etale-zariski-derived-sections-acyclic-leray)

Proof: A continuous finite-limit-preserving i gives an exact inverse image on
abelian sheaves: finite-limit preservation gives representable flatness, hence
left exactness of inverse image on sets; its lift to abelian group objects is
left exact and, being a left adjoint, right exact. Its right adjoint T therefore
preserves injectives. T is left exact as a right adjoint. Choose an injective
resolution I of F. If all positive right-derived images of F vanish, the
augmented complex T(F) -> T(I) is exact: left exactness proves the augmentation
is the degree-zero kernel, and its positive homology is R^q T(F), hence zero.
Every T(I^k) is injective, so T(I) is an injective resolution of T(F).
Evaluation of T(I) at the top open is definitionally evaluation of I at i(top).
Compute right-derived Zariski evaluation using T(I), and right-derived etale
evaluation using I. Their section complexes are identical, giving c F hF n.
For F -> G lift the morphism to a comparison I_F -> I_G. Applying T gives a
comparison of the pushed resolutions. The degreewise section identification
commutes with this comparison, so the resulting homology equivalences satisfy
the displayed naturality equation. Homotopic lifts give equal maps on homology;
proof irrelevance removes dependence on hF and hG. On zero coefficients all
positive groups are zero. Empty schemes cause no exception to the resolution
argument. This assertion has no cohomology/Ext comparison in its conclusion. -/
theorem etaleZariskiDerivedSectionsAcyclicLeray
    (X : Scheme.{u}) (i : X.Opens ⥤ X.Etale)
    [i.IsContinuous (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology]
    [(i.sheafPushforwardContinuous AddCommGrpCat.{u}
      (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).Additive]
    [PreservesFiniteLimits i] :
    let T := i.sheafPushforwardContinuous AddCommGrpCat.{u}
      (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology
    let Z := sheafToPresheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u} ⋙
      (CategoryTheory.evaluation X.Opensᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)
    let E := sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u} ⋙
      (CategoryTheory.evaluation X.Etaleᵒᵖ AddCommGrpCat.{u}).obj (op (i.obj ⊤))
    ∃ c : ∀ (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
        (hF : ∀ n : ℕ, IsZero ((T.rightDerived (n + 1)).obj F)) (n : ℕ),
        ((Z.rightDerived (n + 1)).obj (T.obj F)) ≃+
          ((E.rightDerived (n + 1)).obj F),
      ∀ (F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
        (hF : ∀ n : ℕ, IsZero ((T.rightDerived (n + 1)).obj F))
        (hG : ∀ n : ℕ, IsZero ((T.rightDerived (n + 1)).obj G))
        (φ : F ⟶ G) (n : ℕ) (x : (Z.rightDerived (n + 1)).obj (T.obj F)),
        c G hG n ((Z.rightDerived (n + 1)).map (T.map φ) x) =
          (E.rightDerived (n + 1)).map φ (c F hF n x) := by sorry

end AlgebraicGeometry.Scheme.Modules
