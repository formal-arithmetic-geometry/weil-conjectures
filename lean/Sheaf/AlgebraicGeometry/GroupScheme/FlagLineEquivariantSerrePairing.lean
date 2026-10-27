module

public import Sheaf.AlgebraicGeometry.RhoSectionModules
public import Sheaf.AlgebraicGeometry.GroupScheme.AssociatedCharacterLineBundle
public import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure
public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
public import Sheaf.AlgebraicGeometry.GroupSchemeLinearization
public import Sheaf.AlgebraicGeometry.RelativeDifferentialsPullbackMap
public import Sheaf.Paper.ModuleCohomologyCupProduct
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackMonoidal
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.PQFCohomology
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
public import WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations

import Sheaf.AlgebraicGeometry.GroupScheme.StandardParabolicLeviCharts
import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRankOneReflections
import Sheaf.AlgebraicGeometry.GroupScheme.BorelOppositeRootDichotomy
import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRootSubgroupParametrizations
import Sheaf.AlgebraicGeometry.GroupScheme.BorelRootProductCoordinates

/-! # Equivariant Serre pairing for homogeneous flag lines

Source: Stacks Project, duality.tex, Tags 0FVV and 0FVY,
remark-rework-duality-locally-free-CM; Milne, Algebraic Groups, Section 18c.
(blueprint: lem-sfb-flag-line-equivariant-serre-pairing)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory Opposite
open scoped TensorProduct MonObj
namespace AlgebraicGeometry.FlagSerre

/-- Identify the two existing pullbacks by their adjunctions to the same pushforward.
Source: Stacks, Modules, Tag 0096 (blueprint: lem-sfb-flag-line-equivariant-serre-pairing).
This is the normalized adjoint comparison, not a freely chosen sheaf isomorphism. -/
def pullbackComparison {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Scheme.Modules.tensorPullback f ≅ Scheme.Modules.pullback f :=
  (Scheme.Modules.tensorPullbackSectionAdjunction f).leftAdjointUniq
    (Scheme.Modules.pullbackPushforwardAdjunction f)

/-- Pullback on the recorded derived global sections, followed by the adjoint comparison.
Source: Stacks, Cohomology, Tag 01F7
(blueprint: lem-sfb-flag-line-equivariant-serre-pairing). -/
def pullCohomology {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Y.Modules) (n : ℕ)
    (v : (RingedSpace.moduleCohomology Y.toRingedSpace n).obj L) :
    (RingedSpace.moduleCohomology X.toRingedSpace n).obj
      ((Scheme.Modules.pullback f).obj L) :=
  ((RingedSpace.moduleCohomology X.toRingedSpace n).map
    ((pullbackComparison f).hom.app L))
      (Scheme.Modules.moduleCohomologyPullback f L n v)

/-- The existing derived global sections with scalars restricted along Q → Spec F.
Source: Stacks, duality.tex, Tag 0FVV
(blueprint: lem-sfb-flag-line-equivariant-serre-pairing). -/
abbrev cohomology {F : Type u} [Field F] (Q : Over (Spec (.of F)))
    (L : Q.left.Modules) (n : ℕ) :=
  Scheme.Modules.scalarCohomology Q.hom L n

/-- Scalar extension of evaluation of a right coaction at an algebra-valued group point.
Source: Milne, Section 4a; Stacks, Tag 03LF
(blueprint: lem-sfb-flag-line-equivariant-serre-pairing). -/
def pointAction {F : Type u} [Field F] (G : Grp (Over (Spec (.of F))))
    {V : Type u} [AddCommGroup V] [Module F V]
    (δ : V →ₗ[F] V ⊗[F] RhoSection.Coordinate G.X)
    {A : Type u} [CommRing A] [Algebra F A]
    (s : StandardGroupSchemes.affine F A ⟶ G.X) : A ⊗[F] V →ₗ[A] A ⊗[F] V :=
  TensorProduct.AlgebraTensorModule.lift
    { toFun := fun a ↦ a • ((TensorProduct.comm F V A).toLinearMap ∘ₗ
        (RhoSection.evaluate s).toLinearMap.lTensor V ∘ₗ δ)
      map_add' := fun _ _ ↦ add_smul _ _ _
      map_smul' := fun _ _ ↦ mul_smul _ _ _ }

/-- Pin the existing notion of bundle linearization to the presentation's geometric action.
Source: Milne, Section 18c (blueprint: lem-sfb-flag-line-equivariant-serre-pairing). -/
def IsPresentationLinearization {F : Type u} [Field F]
    {G B : Grp (Over (Spec (.of F)))} {iB : B ⟶ G}
    {Q : Over (Spec (.of F))} {π : G.X ⟶ Q}
    {χ : B ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)}
    (P : AssociatedCharacterLineBundle.Presentation G B iB Q π χ)
    (D : GroupSchemeLinearization.Linearization P.baseAction P.L) : Prop :=
  ∀ (W : Over (Spec (.of F))) (g : W ⟶ G.X) (x : W ⟶ Q)
    (v : Γ((Scheme.Modules.pullback x.left).obj P.L, ⊤)),
    (P.sectionRepresentation W (GroupSchemeLinearization.act P.baseAction W g x)
      ((D.lift W g x).hom.app ⊤ v)).val =
        lift g (P.sectionRepresentation W x v).val ≫ P.totalAction.smul

/-- The inverse universal translation on G × Q.
Source: Milne, Definition 22.21
(blueprint: lem-sfb-flag-line-equivariant-serre-pairing). -/
def inverseTranslation {F : Type u} [Field F] {G : Grp (Over (Spec (.of F)))}
    {Q : Over (Spec (.of F))} (a : ModObj G.X Q) : G.X ⊗ Q ⟶ Q :=
  lift (fst G.X Q)⁻¹ (snd G.X Q) ≫ a.smul

/-- The coaction is the canonical pullback by inverse translation and the bundle action,
compared with scalar extension along G × Q → Q. The displayed finite-sum comparison is
exactly the canonical flat base-change map, characterized on pure tensors. It introduces
neither a freely chosen comparison nor a freely chosen representation.
Source: Stacks, Tag 02KH; Milne, Definition 22.21
(blueprint: lem-sfb-flag-line-equivariant-serre-pairing). -/
def IsInducedCoaction {F : Type u} [Field F] {G : Grp (Over (Spec (.of F)))}
    {Q : Over (Spec (.of F))} {a : ModObj G.X Q} {L : Q.left.Modules}
    (D : GroupSchemeLinearization.Linearization a L) (q : ℕ)
    (δ : cohomology Q L q →ₗ[F] cohomology Q L q ⊗[F] RhoSection.Coordinate G.X) : Prop :=
  ∀ (v : cohomology Q L q) (n : ℕ) (v' : Fin n → cohomology Q L q)
    (c : Fin n → RhoSection.Coordinate G.X), δ v = ∑ i, v' i ⊗ₜ[F] c i →
      ((RingedSpace.moduleCohomology (G.X ⊗ Q).left.toRingedSpace q).map
        (D.lift (G.X ⊗ Q) (fst G.X Q)⁻¹ (snd G.X Q)).inv)
        (pullCohomology (inverseTranslation a).left L q v) =
      ∑ i, (fst G.X Q).left.appTop (c i) •
        pullCohomology (snd G.X Q).left L q (v' i)

/-- The natural cotangent pullback for an F-automorphism, using the existing differential map.
Source: Stacks, Tag 01UV (blueprint: lem-sfb-flag-line-equivariant-serre-pairing). -/
def cotangentMap {F : Type u} [Field F] {Q : Over (Spec (.of F))}
    (h : Q ⟶ Q) :
    (Scheme.Modules.pullback h.left).obj Q.hom.relativeDifferentials ⟶
      Q.hom.relativeDifferentials :=
  ((pullbackComparison h.left).inv.app Q.hom.relativeDifferentials) ≫
    Q.hom.relativeDifferentialsPullbackMap h.left ≫
    (Scheme.Hom.relativeDifferentialsCongr _ h.w).hom

/-- The top wedge and its canonical differential action. Normalization is imposed on
wedges of all local cotangent sections. Since G is smooth over the algebraically closed
field, equality on G(F) determines the algebraic linearization on G × Q; thus this
normalization specifies its action after all algebra extensions, including nonreduced ones.
Source: Stacks, Tags 01UV and 0FVV; Milne, Section 18c
(blueprint: lem-sfb-flag-line-equivariant-serre-pairing). -/
def IsCanonicalLineLinearization {F : Type u} [Field F]
    {G : Grp (Over (Spec (.of F)))} {Q : Over (Spec (.of F))}
    (a : ModObj G.X Q) (N : ℕ)
    (D : GroupSchemeLinearization.Linearization a
      (Scheme.Modules.exteriorSheaf Q.hom.relativeDifferentials N)) : Prop :=
  ∀ (s : 𝟙_ (Over (Spec (.of F))) ⟶ G.X) (U : Q.left.Opens)
    (v : Fin N → Γ(Q.hom.relativeDifferentials, U)),
    ((((D.lift Q ((toUnit Q) ≫ s)⁻¹ (𝟙 Q)).inv) ≫
      (Scheme.Modules.pullbackId Q.left).hom.app
        (Scheme.Modules.exteriorSheaf Q.hom.relativeDifferentials N)).app
      ((GroupSchemeLinearization.act a Q ((toUnit Q) ≫ s)⁻¹ (𝟙 Q)).left ⁻¹ᵁ U))
      (Scheme.Modules.pullbackSection
        (GroupSchemeLinearization.act a Q ((toUnit Q) ≫ s)⁻¹ (𝟙 Q)).left
        (Scheme.Modules.exteriorSheafSection Q.hom.relativeDifferentials N U v)) =
      Scheme.Modules.exteriorSheafSection Q.hom.relativeDifferentials N
        ((GroupSchemeLinearization.act a Q ((toUnit Q) ≫ s)⁻¹ (𝟙 Q)).left ⁻¹ᵁ U)
        (fun i ↦ (cotangentMap
          (GroupSchemeLinearization.act a Q ((toUnit Q) ≫ s)⁻¹ (𝟙 Q))).app
            ((GroupSchemeLinearization.act a Q ((toUnit Q) ≫ s)⁻¹ (𝟙 Q)).left ⁻¹ᵁ U)
            (Scheme.Modules.pullbackSection
              (GroupSchemeLinearization.act a Q ((toUnit Q) ≫ s)⁻¹ (𝟙 Q)).left (v i)))

/-- The canonical product of homogeneous lines, normalized in their common torsor atlas.
All local sections on G are tested, so the condition also determines products when
all global sections on Q vanish.
Source: Milne, Section 18c (blueprint: lem-sfb-flag-line-equivariant-serre-pairing). -/
def IsLineMultiplication {F : Type u} [Field F]
    {G B : Grp (Over (Spec (.of F)))} {iB : B ⟶ G}
    {Q : Over (Spec (.of F))} {π : G.X ⟶ Q}
    {χ ψ ζ : B ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)}
    (P : AssociatedCharacterLineBundle.Presentation G B iB Q π χ)
    (R : AssociatedCharacterLineBundle.Presentation G B iB Q π ψ)
    (W : AssociatedCharacterLineBundle.Presentation G B iB Q π ζ)
    (m : P.L ⊗ R.L ⟶ W.L) : Prop :=
  ∀ (U : G.X.left.Opens)
    (s : Γ((Scheme.Modules.pullback π.left).obj P.L, U))
    (t : Γ((Scheme.Modules.pullback π.left).obj R.L, U)),
    (((Functor.LaxMonoidal.μ (Scheme.Modules.pullback π.left) P.L R.L) ≫
      (Scheme.Modules.pullback π.left).map m ≫ W.trivialization.hom).app U)
        (Scheme.Modules.tmulSection s t) =
      (Scheme.Modules.unitSectionsEquiv U)
        ((Scheme.Modules.unitSectionsEquiv U).symm (P.trivialization.hom.app U s) *
          (Scheme.Modules.unitSectionsEquiv U).symm (R.trivialization.hom.app U t))

/-- The homogeneous canonical line has weight -2 rho, and the cup--trace pairing
is a perfect invariant pairing of the actual finite-dimensional rational cohomology modules.
Source: Stacks, duality.tex, Tag 0FVV (6),(7), Tag 0FVY and
remark-rework-duality-locally-free-CM; Andersen, Lemma 4, proof p.58, canonical-character
specialization (blueprint: lem-sfb-flag-line-equivariant-serre-pairing).

Proof plan:
1. Apply lem-sfb-standard-parabolic-levi-charts at the empty set and B minus.
   The quotient is proper and its atlas is a smooth B minus torsor.
   Lemma lem-sfb-homogeneous-cotangent-associated-bundle identifies its cotangent
   with the associated dual of Lie(S)/Lie(B minus).
2. The weight decomposition from lem-sfb-reductive-rank-one-reflections and
   lem-sfb-borel-opposite-root-dichotomy cancels the torus and negative roots.
   Each positive root occurs once. The dual determinant has character -2 rho
   and rank N, including the empty wedge in rank zero.
3. By lem-sfb-reductive-root-subgroup-parametrizations each root group is Ga.
   A character Ga → Gm is trivial because units of F[t] are constants and the
   identity has value one. Lemma lem-sfb-borel-root-product-coordinates then
   makes the determinant character trivial on the unipotent radical. The
   semidirect product of lem-sfb-reductive-borel-pair-structure identifies it
   with the extension of -2 rho. Associated descent gives the canonical-line iso.
4. Tensor products of homogeneous lines multiply their character transition
   functions. Their local multiplication maps glue, commute with translation,
   and identify the dual line tensor omega with L(-y-2 rho). Apply
   lem-sfb-linearized-qcoherent-cohomology-coaction to obtain the induced
   rational coactions, characterized here by inverse universal translation.
5. Apply lem-sfb-smooth-proper-coherent-trace-pairing to Q and L(y).
   Transport its trace through the canonical-line iso. Its cup--evaluation
   product is precisely the normalized line multiplication below. Both factors
   are finite-dimensional and both curried duality maps are bijective.
6. Apply the automorphism naturality and arbitrary-algebra base change of
   lem-sfb-smooth-proper-coherent-trace-pairing to inverse translation by s.
   Evaluate at the universal point of S to obtain the trace and pairing
   coaction identities. They imply invariance over every commutative algebra.
   Every step includes N=0 and characteristic two; no division in F is used. -/
theorem flagLine_equivariant_serre_pairing
    {F : Type u} [Field F] [IsAlgClosed F] (pchar : ℕ) [CharP F pchar]
    (hpchar : 0 < pchar) (S : Grp (Over (Spec (.of F))))
    (hS : IsSemisimpleGroupScheme S.X)
    (hsc : ∀ (S' : Over (Spec (.of F))) [GrpObj S'],
      IsSemisimpleGroupScheme S' → ∀ (f : S' ⟶ S.X) [IsMonHom f],
      Surjective f.left → IsFinite (GrpObj.ker f).hom →
      (∀ (A : Type u) [CommRing A] [Algebra F A]
        (x : StandardGroupSchemes.affine F A ⟶ GrpObj.ker f)
        (s : StandardGroupSchemes.affine F A ⟶ S'),
        (x ≫ GrpObj.kerι f) * s = s * (x ≫ GrpObj.kerι f)) → IsIso f)
    (T B Bm : Grp (Over (Spec (.of F))))
    (iT : T ⟶ S) (iB : B ⟶ S) (j : T ⟶ B)
    (hpair : IsRhoBorelPair iT iB j)
    (iBm : Bm ⟶ S) (jm : T ⟶ Bm) (hpairm : IsRhoBorelPair iT iBm jm)
    (aB : ModObj T.X B.X) (aBm : ModObj T.X Bm.X)
    (haB : aB.smul = (j.hom.hom ⊗ₘ 𝟙 B.X) ≫ GrpObj.conj B.X)
    (haBm : aBm.smul = (jm.hom.hom ⊗ₘ 𝟙 Bm.X) ≫ GrpObj.conj Bm.X)
    (Φ : List (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
    (hΦ : Φ.Nodup)
    (hpos : ∀ α, α ∈ Φ ↔ α.hom.hom ≠ 1 ∧
      @TorusCharacterTangent.weightSpace F _ T B aB α ≠ ⊥)
    (hneg : ∀ α : T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F),
      (α.hom.hom ≠ 1 ∧ @TorusCharacterTangent.weightSpace F _ T Bm aBm α ≠ ⊥) ↔
        ∃ β ∈ Φ, α.hom.hom = β.hom.hom⁻¹)
    (ρ : T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))
    (hρ : ρ.hom.hom ^ 2 = (Φ.map (fun α ↦ α.hom.hom)).prod)
    (pr : Bm ⟶ T) (hpr : jm ≫ pr = 𝟙 T)
    (hprU : ∀ (U : Grp (Over (Spec (.of F)))) (l : U ⟶ Bm),
      IsClosedSubgroupScheme l.hom.hom → IsNormalSubgroupScheme l.hom.hom →
      ConnectedSpace U.X.left → SolvableGroupStructure.IsUnipotent U →
        l.hom.hom ≫ pr.hom.hom = 1)
    (Q : Over (Spec (.of F))) (π : S.X ⟶ Q)
    (hQ : IsProper Q.hom) (hQft : LocallyOfFiniteType Q.hom)
    (hπflat : Flat π.left) (hπsurj : Surjective π.left)
    (hπinv : (fst S.X Bm.X * (snd S.X Bm.X ≫ iBm.hom.hom)) ≫ π =
      fst S.X Bm.X ≫ π)
    (hπtorsor : IsPullback (fst S.X Bm.X)
      (fst S.X Bm.X * (snd S.X Bm.X ≫ iBm.hom.hom)) π π)
    (P : ∀ y : T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F),
      AssociatedCharacterLineBundle.Presentation S Bm iBm Q π (pr ≫ y)) :
    ∃ (w : T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)),
      w.hom.hom = (ρ.hom.hom ^ 2)⁻¹ ∧
    ∃ (D : ∀ y, GroupSchemeLinearization.Linearization (P y).baseAction (P y).L),
      (∀ y, IsPresentationLinearization (P y) (D y)) ∧
    ∃ (Dω : GroupSchemeLinearization.Linearization (P w).baseAction
        (Scheme.Modules.exteriorSheaf Q.hom.relativeDifferentials Φ.length))
      (e : Scheme.Modules.exteriorSheaf Q.hom.relativeDifferentials Φ.length ≅ (P w).L),
      IsCanonicalLineLinearization (P w).baseAction Φ.length Dω ∧
      (∀ (W : Over (Spec (.of F))) (s : W ⟶ S.X) (x : W ⟶ Q),
        (Scheme.Modules.pullback x.left).map e.hom ≫ ((D w).lift W s x).hom =
          (Dω.lift W s x).hom ≫
            (Scheme.Modules.pullback
              (GroupSchemeLinearization.act (P w).baseAction W s x).left).map e.hom) ∧
    ∃ (δ : ∀ y (i : ℕ), cohomology Q (P y).L i →ₗ[F]
        cohomology Q (P y).L i ⊗[F] RhoSection.Coordinate S.X),
      (∀ y i, (∀ (A : Type u) [CommRing A] [Algebra F A],
        pointAction S (δ y i) (1 : StandardGroupSchemes.affine F A ⟶ S.X) =
          LinearMap.id ∧
        ∀ (s t : StandardGroupSchemes.affine F A ⟶ S.X),
          pointAction S (δ y i) (s * t) =
            (pointAction S (δ y i) s).comp (pointAction S (δ y i) t)) ∧
        IsInducedCoaction (D y) i (δ y i)) ∧
    ∃ tr : cohomology Q (P w).L Φ.length →ₗ[F] F,
      (∀ v, tr.rTensor (RhoSection.Coordinate S.X) (δ w Φ.length v) =
        tr v ⊗ₜ[F] (1 : RhoSection.Coordinate S.X)) ∧
    ∀ (y z : T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)),
      z.hom.hom = y.hom.hom⁻¹ * w.hom.hom →
    ∀ i : ℕ, i ≤ Φ.length →
      Module.Finite F (cohomology Q (P y).L i) ∧
      Module.Finite F (cohomology Q (P z).L (Φ.length - i)) ∧
    ∃ (m : (P y).L ⊗ (P z).L ≅ (P w).L)
      (cup : (RingedSpace.moduleCohomology Q.left.toRingedSpace i).obj (P y).L →ₗ[Γ(Q.left, ⊤)]
        (RingedSpace.moduleCohomology Q.left.toRingedSpace (Φ.length - i)).obj
          (P z).L →ₗ[Γ(Q.left, ⊤)]
        (RingedSpace.moduleCohomology Q.left.toRingedSpace (i + (Φ.length - i))).obj
          (@id Q.left.Modules ((P y).L ⊗ (P z).L)))
      (b : cohomology Q (P y).L i →ₗ[F]
        cohomology Q (P z).L (Φ.length - i) →ₗ[F] F),
      IsLineMultiplication (P y) (P z) (P w) m.hom ∧
      Scheme.Modules.IsModuleCupProduct (P y).L (P z).L i (Φ.length - i) cup ∧
      (∃ h : i + (Φ.length - i) = Φ.length,
        ∀ x v, b x v = tr
          ((eqToHom (congrArg (fun n ↦
            (RingedSpace.moduleCohomology Q.left.toRingedSpace n).obj (P w).L) h))
            (((RingedSpace.moduleCohomology Q.left.toRingedSpace
              (i + (Φ.length - i))).map m.hom) (cup x v)))) ∧
      Function.Bijective b ∧ Function.Bijective b.flip ∧
      (∀ (x : cohomology Q (P y).L i)
        (v : cohomology Q (P z).L (Φ.length - i)) (n k : ℕ)
        (x' : Fin n → cohomology Q (P y).L i)
        (v' : Fin k → cohomology Q (P z).L (Φ.length - i))
        (c : Fin n → RhoSection.Coordinate S.X)
        (d : Fin k → RhoSection.Coordinate S.X),
        δ y i x = ∑ j, x' j ⊗ₜ[F] c j →
        δ z (Φ.length - i) v = ∑ j, v' j ⊗ₜ[F] d j →
        ∑ j, ∑ l, c j * d l * algebraMap F (RhoSection.Coordinate S.X) (b (x' j) (v' l)) =
          algebraMap F (RhoSection.Coordinate S.X) (b x v)) := by
  sorry

end AlgebraicGeometry.FlagSerre
