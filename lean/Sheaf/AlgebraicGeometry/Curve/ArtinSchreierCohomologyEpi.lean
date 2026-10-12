module

public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import Sheaf.AlgebraicGeometry.EtaleAffineQcoherentULift
import Sheaf.AlgebraicGeometry.EtaleZariskiQcohComparison
import Sheaf.CategoryTheory.KInjectiveComputes
import Sheaf.CategoryTheory.RightDerivedUniversalDeltaFunctor
import Sheaf.Paper.PQFCohomology
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex
import WeilConjectures.AlgebraicGeometry.Curve.Compactification
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle
import WeilConjectures.LinearAlgebra.SemilinearFrobenius


@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Frobenius minus identity is onto in first additive cohomology of a curve.
Source: blueprint `lem-sc-artin-schreier-dimension`, steps 3--7; Stacks 0A3L and 0A3N.
(blueprint: lem-sc-artin-schreier-first-cohomology-epi)

Proof: The natural section equivalences identify G with the additive etale
structure sheaf and wp with x ↦ x^p-x. Compactify the smooth connected curve;
it is either proper or affine (lem-sc-compactification, lem-sc-affine-open-proper).
In the affine case its first additive cohomology vanishes by
lem-sc-etale-affine-qcoherent, so every endomorphism is onto.
In the proper case scalar multiplication on sections induces a k-vector-space
structure on H^1(C,G). Additivity of cohomology transports the sectionwise
relations for scalar multiplication, Frobenius, and subtraction, so H^1(wp)
is F-1 for a p-semilinear F. Naturality of the etale/Zariski comparison
(lem-sc-etale-zariski-qcoh-comparison) identifies this vector space linearly
with H^1(C,O_C). Proper coherent cohomology is finite dimensional by
lem-pc-coherent-hi and pqf-def-cohomology. Lang--Steinberg
(lem-sc-lang-steinberg, Stacks 0A3L) gives surjectivity of F-1. The natural
injective-resolution comparison with derived global sections preserves this
map, and surjectivity in additive groups is equivalent to epimorphy. The
universe comparisons can be made on finite affine etale hypercover cochains
(quasi-compactness supplies finite refinements in each relevant degree). Lifting
identifies cocycles, coboundaries, and the maps induced by wp; one need not
assume that universe lift preserves injective sheaves. -/
theorem epi_etaleCohomology_artinSchreier_one
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f]
    (p : ℕ) [Fact p.Prime] [CharP k p]
    (G : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1})
    (a : ∀ U : C.Etaleᵒᵖ, G.obj.obj U ≃+ Γ(U.unop.left, ⊤))
    (wp : G ⟶ G)
    (ha : ∀ (U V : C.Etaleᵒᵖ) (g : U ⟶ V) (x : G.obj.obj U),
      a V (G.obj.map g x) = g.unop.left.appTop (a U x))
    (hwp : ∀ (U : C.Etaleᵒᵖ) (x : G.obj.obj U),
      a U (wp.hom.app U x) = (a U x) ^ p - a U x) :
    Epi ((Etale.cohomology AddCommGrpCat.{u + 1} C (1 : ℤ)).map
      ((DerivedCategory.singleFunctor
        (Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).map wp)) := by
  sorry

end AlgebraicGeometry
