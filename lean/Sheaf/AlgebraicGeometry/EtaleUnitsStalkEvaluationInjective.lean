module

public import WeilConjectures.AlgebraicGeometry.Sites.Gm
public import Sheaf.FieldTheory.GaloisUnitsCohomology
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.CategoryTheory.Sites.Torsor
import WeilConjectures.Mathlib.RingTheory.Etale.Field

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

/-- Injectivity part of geometric stalk evaluation.

Source: Stacks Project, Tags 03QU and Example 03QV (2).
(blueprint: lem-sc-etale-units-stalk-evaluation-injective).

Proof: Represent two stalk elements by unit germs on pointed etale neighbourhoods.
Choose an affine open around the image of each geometric lift. An etale algebra
of finite type over a field is a finite product of finite separable extensions;
restrict to the factor selected by the lift. Thus both germs are represented on
spectra of finite separable fields embedded in the algebraic closure. The
compositum of their images is again finite separable over K, so its spectrum is
a common pointed etale refinement. If the two images under f agree, the
evaluation formula makes their values in the algebraic closure equal. The
embedding of the compositum is injective, hence the pulled-back units have equal
underlying values and are equal as units. Restriction preserves their germs, so
their images in the filtered colimit defining the stalk agree. This proves
injectivity. Only separable extensions are used, including when K is imperfect. -/
theorem etale_units_stalk_evaluation_injective (K : Type u) [Field K] :
    let Ω := AlgebraicClosure K
    let S := Spec (.of K)
    let p := pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
    ∀ f : (p.sheafFiber (A := AddCommGrpCat.{u + 1})).obj S.gmSheaf →+
        Field.galoisUnitsTopRep K,
      (∀ (X : S.Etale) (x : p.fiber.obj X) (z : S.gmSheaf.obj.obj (op X)),
        algebraMap (SeparableClosure K) Ω
            (Additive.toMul (f (p.toPresheafFiber X x S.gmSheaf.obj z)) :
              (SeparableClosure K)ˣ) =
          (ΓSpecIso (.of Ω)).hom
            (x.left.appTop ((Additive.toMul z.down : Γ(X.left, ⊤)ˣ) : Γ(X.left, ⊤)))) →
      Function.Injective f := by
  sorry

end AlgebraicGeometry.Scheme
