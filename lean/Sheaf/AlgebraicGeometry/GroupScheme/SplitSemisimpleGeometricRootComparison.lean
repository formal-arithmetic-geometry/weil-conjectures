module

public import Sheaf.AlgebraicGeometry.GroupScheme.RankOneRootInterfaces
public import Sheaf.AlgebraicGeometry.GroupScheme.Borel
public import Mathlib.LinearAlgebra.RootSystem.Base
public import Mathlib.LinearAlgebra.RootSystem.Reduced
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Order.SupIndep
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected
import Sheaf.AlgebraicGeometry.RelativeSplitTorusMatrixSheaf
import Sheaf.RepresentationTheory.RelativeTorusBundleWeights
import Sheaf.AlgebraicGeometry.ReductiveTorusSelfCentralizer
import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure
import Sheaf.AlgebraicGeometry.GroupScheme.BorelRootProductCoordinates
import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRootSubgroupParametrizations

/-! # Geometric scalar extension of a split semisimple root datum

Source: Milne, Algebraic Groups (2017), 21.11--21.12, 21.17, 21.29--21.35,
23.56 and 23.58--23.59, printed pp.428--435 and 501--502.
(blueprint: lem-sfb-split-semisimple-geometric-root-comparison)

Characters and cocharacters are the actual additive group-scheme Hom groups.
The multiplicative-group comparison is pinned by its Laurent coordinate, and the
linear tangent comparison by its dual-number points. Weight-space compatibility
for every character, including zero, expresses equivariance for the split torus.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj TensorProduct

namespace AlgebraicGeometry

/-- Scalar extension preserves the split simply connected semisimple root datum,
its tangent weight spaces, and realizes any chosen positive system by a Borel with
its unipotent radical and the specified semidirect product decomposition.

Source: Milne, 21.11--21.12, 21.17, 21.29--21.35, 23.56, 23.58--23.59.
(blueprint: lem-sfb-split-semisimple-geometric-root-comparison)

Proof plan:
1. Smoothness and affineness survive base change by lem-pc-proper-base-change and
   lem-weil-pbc-affine-morphism-permanence. Finite algebra generators extend.
   The identity section and lem-sbc-connected-rational-point-geometrically-connected
   give geometric connectedness. The assumed geometric semisimplicity excludes
   normal unipotent groups, since lem-sfb-smooth-unipotent-solvable makes them solvable.
   Apply lem-sfb-geometric-neutral-reductivity-field-invariance and the affine smooth
   criterion lem-weil-pbc-smooth-ring-map-iff-smooth-affine to get reductivity.
   Base change of the split-torus isomorphism gives splitness; maximality is assumed.
2. By lem-sfb-relative-split-torus-matrix-sheaf, character and cocharacter maps are
   unchanged integer row and column vectors. Their composition is the dot product,
   so the actual extension maps are mutually bijective and preserve the pairing.
3. The dual-number comparison of lem-sfb-affine-group-lie-tangent-calculus commutes
   with conjugation. Apply lem-sfb-relative-torus-bundle-weights to the adjoint
   coaction to identify every extended weight space, including the zero weight.
   Extending a basis preserves nonzero weight spaces, so exactly the roots correspond.
4. The centralizer equality of lem-sfb-reductive-torus-self-centralizer persists
   on all extension algebras and proves geometric maximality. Apply
   lem-sfb-arbitrary-base-root-lines-coroots to identify the normalized coroots.
   The formulas x - <x,alpha-vee>alpha and y - <alpha,y>alpha-vee then commute
   with the lattice maps, giving both reflection identities.
5. Apply lem-sfb-split-semisimple-weight-lattice-criterion over k: simple
   connectedness says X is the full weight lattice. Pairing preservation identifies
   its integrality conditions after extension. Apply the converse criterion over F.
6. By lem-sfb-semisimple-roots-span, the simple roots are a rational basis. The
   functional taking value one on each simple root is positive exactly on the
   chosen positive roots. The perfect pairing identifies it with a rational
   cocharacter; clearing a positive common denominator gives an integral regular
   cocharacter with the same signs. For rank zero use the zero cocharacter.
7. Apply lem-sfb-regular-cocharacter-borel-description to that cocharacter.
   Apply lem-sfb-reductive-borel-pair-structure for its largest smooth connected
   normal unipotent subgroup and its torus complement. By
   lem-sfb-borel-root-product-coordinates, multiplication of positive root subgroups
   is an isomorphism onto the radical. Their tangent spaces are the root spaces by
   lem-sfb-reductive-root-subgroup-parametrizations. Differentiation of multiplication
   adds tangent vectors, giving the independent sum and its equality with Lie(U).
   The empty product gives the trivial radical in rank zero. -/
theorem splitSemisimple_geometric_root_comparison
    {k F : Type u} [Field k] [CharZero k] [Field F] [Algebra k F]
    [IsAlgClosed F] [IsAlgClosure k F]
    (G T : Grp (Over (Spec (.of k))))
    (hGs : Smooth G.X.hom) (hGc : ConnectedSpace G.X.left)
    (hGa : IsAffine G.X.left) (hGft : LocallyOfFiniteType G.X.hom)
    (hGqc : QuasiCompact G.X.hom)
    (hGss : IsSemisimpleGroupScheme ((MultiplicativeType.baseChange (K := F)).obj G).X)
    (hsc : ∀ (H : Grp (Over (Spec (.of k)))),
      Smooth H.X.hom → ConnectedSpace H.X.left → IsAffine H.X.left →
      LocallyOfFiniteType H.X.hom → QuasiCompact H.X.hom →
      IsSemisimpleGroupScheme ((MultiplicativeType.baseChange (K := F)).obj H).X →
      ∀ (f : H ⟶ G), Surjective f.hom.hom.left →
      IsFinite (GrpObj.ker f.hom.hom).hom →
      (∀ (A : Type u) [CommRing A] [Algebra k A]
        (x : StandardGroupSchemes.affine k A ⟶ GrpObj.ker f.hom.hom)
        (g : StandardGroupSchemes.affine k A ⟶ H.X),
        (x ≫ GrpObj.kerι f.hom.hom) * g = g * (x ≫ GrpObj.kerι f.hom.hom)) →
      IsIso f)
    (i : T ⟶ G) (hi : IsClosedSubgroupScheme i.hom.hom)
    (r : ℕ) (hsplit : Nonempty (T ≅ MultiplicativeType.splitTorus k r))
    (hmax : ReductiveTorusCentralizer.IsMaximalTorus
      ((MultiplicativeType.baseChange (K := F)).map i))
    [IsCommMonObj T.X] [IsCommMonObj (StandardGroupSchemes.multiplicative k)]
    (aG : ModObj T.X G.X) (haG : aG.smul = RankOneRoots.adjointMap i)
    (Φ : Finset (Additive (RankOneRoots.Character T)))
    (P : RootDatum Φ (Additive (RankOneRoots.Character T))
      (Additive (RankOneRoots.Cocharacter T))) (b : P.Base)
    (hroot : ∀ α : Φ, P.root α = α.val)
    (hpair : ∀ (χ : Additive (RankOneRoots.Character T))
      (ν : Additive (RankOneRoots.Cocharacter T)),
      ν.toMul.hom.hom ≫ χ.toMul.hom.hom =
        (𝟙 (StandardGroupSchemes.multiplicative k)) ^ (P.toLinearMap χ ν))
    (hweights : ∀ χ : Additive (RankOneRoots.Character T),
      χ ∈ Φ ↔ χ ≠ 0 ∧ RankOneRoots.weight T G aG χ.toMul ≠ ⊥) :
    IsSemisimpleGroupScheme ((MultiplicativeType.baseChange (K := F)).obj G).X ∧
    (∀ (H : Grp (Over (Spec (.of F)))), IsSemisimpleGroupScheme H.X →
      ∀ (f : H ⟶ (MultiplicativeType.baseChange (K := F)).obj G),
      Surjective f.hom.hom.left → IsFinite (GrpObj.ker f.hom.hom).hom →
      (∀ (A : Type u) [CommRing A] [Algebra F A]
        (x : StandardGroupSchemes.affine F A ⟶ GrpObj.ker f.hom.hom)
        (g : StandardGroupSchemes.affine F A ⟶ H.X),
        (x ≫ GrpObj.kerι f.hom.hom) * g = g * (x ≫ GrpObj.kerι f.hom.hom)) →
      IsIso f) ∧
    ReductiveTorusCentralizer.IsMaximalTorus
      ((MultiplicativeType.baseChange (K := F)).map i) ∧
    Nonempty ((MultiplicativeType.baseChange (K := F)).obj T ≅
      MultiplicativeType.splitTorus F r) ∧
    ∃ (_ : IsCommMonObj ((MultiplicativeType.baseChange (K := F)).obj T).X)
      (_ : IsCommMonObj (StandardGroupSchemes.multiplicative F))
      (m : (MultiplicativeType.baseChange (K := F)).obj
        (Grp.mk (StandardGroupSchemes.multiplicative k)) ≅
        Grp.mk (StandardGroupSchemes.multiplicative F))
      (ex : Additive (RankOneRoots.Character T) ≃ₗ[ℤ]
        Additive (RankOneRoots.Character ((MultiplicativeType.baseChange (K := F)).obj T)))
      (ey : Additive (RankOneRoots.Cocharacter T) ≃ₗ[ℤ]
        Additive (RankOneRoots.Cocharacter ((MultiplicativeType.baseChange (K := F)).obj T)))
      (PF : RootDatum Φ
        (Additive (RankOneRoots.Character ((MultiplicativeType.baseChange (K := F)).obj T)))
        (Additive (RankOneRoots.Cocharacter ((MultiplicativeType.baseChange (K := F)).obj T))))
      (aF : ModObj ((MultiplicativeType.baseChange (K := F)).obj T).X
        ((MultiplicativeType.baseChange (K := F)).obj G).X)
      (d : DualNumber k →+* DualNumber F)
      (l : F ⊗[k] GrpObj.Lie G.X ≃ₗ[F]
        GrpObj.Lie ((MultiplicativeType.baseChange (K := F)).obj G).X),
      (Scheme.ΓSpecIso (.of (LaurentPolynomial F))).hom
        ((m.inv.hom.hom.left ≫
          pullback.fst (StandardGroupSchemes.multiplicative k).hom
            (Spec.map (CommRingCat.ofHom (algebraMap k F)))).appTop
          ((Scheme.ΓSpecIso (.of (LaurentPolynomial k))).inv (LaurentPolynomial.T 1))) =
        LaurentPolynomial.T 1 ∧
      (∀ χ : Additive (RankOneRoots.Character T),
        (ex χ).toMul = (MultiplicativeType.baseChange (K := F)).map χ.toMul ≫ m.hom) ∧
      (∀ ν : Additive (RankOneRoots.Cocharacter T),
        (ey ν).toMul = m.inv ≫ (MultiplicativeType.baseChange (K := F)).map ν.toMul) ∧
      (∀ (χ : Additive (RankOneRoots.Character T))
        (ν : Additive (RankOneRoots.Cocharacter T)),
        PF.toLinearMap (ex χ) (ey ν) = P.toLinearMap χ ν) ∧
      (∀ α : Φ, PF.root α = ex (P.root α) ∧ PF.coroot α = ey (P.coroot α)) ∧
      (∀ (α : Φ) (χ : Additive (RankOneRoots.Character T)),
        ex (P.reflection α χ) = PF.reflection α (ex χ)) ∧
      (∀ (α : Φ) (ν : Additive (RankOneRoots.Cocharacter T)),
        ey (P.coreflection α ν) = PF.coreflection α (ey ν)) ∧
      aF.smul = RankOneRoots.adjointMap ((MultiplicativeType.baseChange (K := F)).map i) ∧
      (∀ χ : Additive (RankOneRoots.Character ((MultiplicativeType.baseChange (K := F)).obj T)),
        χ ∈ Set.range PF.root ↔ χ ≠ 0 ∧
          RankOneRoots.weight ((MultiplicativeType.baseChange (K := F)).obj T)
            ((MultiplicativeType.baseChange (K := F)).obj G) aF χ.toMul ≠ ⊥) ∧
      (∀ z : DualNumber k,
        (d z).fst = algebraMap k F z.fst ∧ (d z).snd = algebraMap k F z.snd) ∧
      (∀ v : GrpObj.Lie G.X,
        (GrpObj.tangentPoint (l (1 ⊗ₜ[k] v))).left ≫
          pullback.fst G.X.hom (Spec.map (CommRingCat.ofHom (algebraMap k F))) =
        Spec.map (CommRingCat.ofHom d) ≫ (GrpObj.tangentPoint v).left) ∧
      (∀ χ : Additive (RankOneRoots.Character T),
        ((RankOneRoots.weight T G aG χ.toMul).baseChange F).map l.toLinearMap =
          RankOneRoots.weight ((MultiplicativeType.baseChange (K := F)).obj T)
            ((MultiplicativeType.baseChange (K := F)).obj G) aF (ex χ).toMul) ∧
      ∃ (B : Grp (Over (Spec (.of F))))
        (iB : B ⟶ (MultiplicativeType.baseChange (K := F)).obj G)
        (j : (MultiplicativeType.baseChange (K := F)).obj T ⟶ B),
        IsBorelGroupScheme iB.hom.hom ∧
        j ≫ iB = (MultiplicativeType.baseChange (K := F)).map i ∧
        (∀ α : Φ, b.IsPos α ↔
          RankOneRoots.weight ((MultiplicativeType.baseChange (K := F)).obj T)
            ((MultiplicativeType.baseChange (K := F)).obj G) aF (ex α.val).toMul ≤
              (GrpObj.differential iB.hom.hom).toLinearMap.range) ∧
        ∃ (U : Grp (Over (Spec (.of F)))) (iU : U ⟶ B)
          (p : B ⟶ (MultiplicativeType.baseChange (K := F)).obj T),
          IsClosedSubgroupScheme iU.hom.hom ∧ IsNormalSubgroupScheme iU.hom.hom ∧
          Smooth U.X.hom ∧ ConnectedSpace U.X.left ∧ SolvableGroupStructure.IsUnipotent U ∧
          (∀ (N : Grp (Over (Spec (.of F)))) (iN : N ⟶ B),
            IsClosedSubgroupScheme iN.hom.hom → IsNormalSubgroupScheme iN.hom.hom →
            Smooth N.X.hom → ConnectedSpace N.X.left → SolvableGroupStructure.IsUnipotent N →
              ∃ f : N ⟶ U, f ≫ iU = iN) ∧
          j ≫ p = 𝟙 _ ∧
          IsPullback iU.hom.hom (toUnit U.X) p.hom.hom η[_] ∧
          IsIso ((fst U.X ((MultiplicativeType.baseChange (K := F)).obj T).X ≫ iU.hom.hom) *
            (snd U.X ((MultiplicativeType.baseChange (K := F)).obj T).X ≫ j.hom.hom)) ∧
          iSupIndep (fun α : {α : Φ // b.IsPos α} ↦
            RankOneRoots.weight ((MultiplicativeType.baseChange (K := F)).obj T)
              ((MultiplicativeType.baseChange (K := F)).obj G) aF (ex α.val.val).toMul) ∧
          (GrpObj.differential (iU ≫ iB).hom.hom).toLinearMap.range =
            ⨆ α : {α : Φ // b.IsPos α},
              RankOneRoots.weight ((MultiplicativeType.baseChange (K := F)).obj T)
                ((MultiplicativeType.baseChange (K := F)).obj G) aF (ex α.val.val).toMul := by
  sorry

end AlgebraicGeometry
