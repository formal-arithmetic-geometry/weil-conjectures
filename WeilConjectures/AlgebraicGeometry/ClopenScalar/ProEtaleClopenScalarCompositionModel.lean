/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ClopenScalar.ProEtaleClopenScalarComputation

/-! # Normalized clopen scalar comparison

Source: Stacks Project, Tags 06YY and 0D6D.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe t u w
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
open SheafOfModules SheafOfModules.SuccessiveDerivedQuotient
namespace AlgebraicGeometry.Scheme.ProEt.ClopenScalar
attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] ClopenLocalization.modulesAbelian ClopenLocalization.hasDerived
attribute [-instance] ClopenLocalization.sheafify ClopenLocalization.locallyBijective

set_option maxHeartbeats 400000 in
-- Rewriting in composites of derived functors requires large instance-level unification.
/-- The right-hand path of the composition square, postcomposed with the restricted
computation, as a computation followed by the termwise comparisons.
Source: Stacks 06YY, 0D6D (auxiliary; not a blueprint node). -/
private theorem composition_model_right
    {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    {p : Presentations.{t, u} X} {q : Presentations.{t, u} Y}
    (m : Normalization.{t + 1, t, max u (t + 1), max (u + 1) (t + 2)}
      (C := Y.ProEt) (J := topology Y) (hD := derived.{t, u} Y) @q)
    (d : Comparison.{t, u} j @p @q) (hrep : d.representative)
    {R S T : Sheaf (topology X) CommRingCat.{max u (t + 1)}}
    (a : R ⟶ S) (b : S ⟶ T)
    (P : CochainComplex (Mods.{t, u} R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients.{t + 1, t, max u (t + 1)} (R := R) P)
    (hf : ∀ k : ℤ, IsFlatOnSite.{t + 1, t, max u (t + 1), max u (t + 1)} (J := topology X)
      (R := R) (P.X k))
    (hiP : CochainComplex.IsKFlatIndependentCoefficients.{t + 1, t, max u (t + 1)}
      (R := (rings.{t, u} j).obj R) (((res.{t, u} j R).mapHomologicalComplex (.up ℤ)).obj P))
    (hif : ∀ k : ℤ, IsFlatOnSite.{t + 1, t, max u (t + 1), max u (t + 1)} (J := topology Y)
      (R := (rings.{t, u} j).obj R) ((res.{t, u} j R).obj (P.X k)))
    (hK : CochainComplex.IsKFlatIndependentCoefficients.{t + 1, t, max u (t + 1)} (R := S)
      (((ext.{t, u} (Z := X) (p a)).mapHomologicalComplex (.up ℤ)).obj P))
    (hF : ∀ k : ℤ, IsFlatOnSite.{t + 1, t, max u (t + 1), max u (t + 1)} (J := topology X)
      (R := S) ((ext.{t, u} (Z := X) (p a)).obj (P.X k))) :
    (d.derived b).hom.app ((extD.{t, u} (Z := X) (p a)).obj (DerivedCategory.Q.obj P)) ≫
        (extD (q ((rings.{t, u} j).map b))).map ((d.derived a).hom.app (DerivedCategory.Q.obj P)) ≫
        (m.derived ((rings.{t, u} j).map a) ((rings.{t, u} j).map b)).hom.app
          ((resD.{t, u} j R).obj (DerivedCategory.Q.obj P)) ≫
        (extD (q ((rings.{t, u} j).map a ≫ (rings.{t, u} j).map b))).map
          ((res.{t, u} j R).mapDerivedCategoryFactors.hom.app P) ≫
        computation (q ((rings.{t, u} j).map a ≫ (rings.{t, u} j).map b))
          (((res.{t, u} j R).mapHomologicalComplex (.up ℤ)).obj P) =
      (resD.{t, u} j T).map ((extD (p b)).map (computation (p a) P)) ≫
        (resD.{t, u} j T).map
          (computation (p b) (((ext.{t, u} (Z := X) (p a)).mapHomologicalComplex (.up ℤ)).obj P)) ≫
        (res.{t, u} j T).mapDerivedCategoryFactors.hom.app
          (((ext.{t, u} (Z := X) (p b)).mapHomologicalComplex (.up ℤ)).obj
            (((ext.{t, u} (Z := X) (p a)).mapHomologicalComplex (.up ℤ)).obj P)) ≫
        DerivedCategory.Q.map
          ((d.chain b).hom.app (((ext.{t, u} (Z := X) (p a)).mapHomologicalComplex (.up ℤ)).obj P) ≫
            ((ext.{t, u} (Z := Y) (q ((rings.{t, u} j).map b))).mapHomologicalComplex (.up ℤ)).map
              ((d.chain a).hom.app P) ≫
            (Functor.mapHomologicalComplexCompIso
              (m.ordinary ((rings.{t, u} j).map a) ((rings.{t, u} j).map b)) (.up ℤ)).hom.app
              (((res.{t, u} j R).mapHomologicalComplex (.up ℤ)).obj P)) := by
  have hm : (m.derived ((rings.{t, u} j).map a) ((rings.{t, u} j).map b)).hom.app
        ((resD.{t, u} j R).obj (DerivedCategory.Q.obj P)) ≫
        (extD (q ((rings.{t, u} j).map a ≫ (rings.{t, u} j).map b))).map
          ((res.{t, u} j R).mapDerivedCategoryFactors.hom.app P) =
      (extD (q ((rings.{t, u} j).map b))).map ((extD (q ((rings.{t, u} j).map a))).map
          ((res.{t, u} j R).mapDerivedCategoryFactors.hom.app P)) ≫
        (m.derived ((rings.{t, u} j).map a) ((rings.{t, u} j).map b)).hom.app
          (DerivedCategory.Q.obj (((res.{t, u} j R).mapHomologicalComplex (.up ℤ)).obj P)) :=
    ((m.derived _ _).hom.naturality _).symm
  rw [reassoc_of% hm]
  rw [normalization_derived_hom_app_comp_computation m ((rings.{t, u} j).map a)
    ((rings.{t, u} j).map b) _ hiP hif]
  have hA : (extD (q ((rings.{t, u} j).map b))).map
        ((d.derived a).hom.app (DerivedCategory.Q.obj P)) ≫
      (extD (q ((rings.{t, u} j).map b))).map ((extD (q ((rings.{t, u} j).map a))).map
          ((res.{t, u} j R).mapDerivedCategoryFactors.hom.app P)) ≫
      (extD (q ((rings.{t, u} j).map b))).map (computation (q ((rings.{t, u} j).map a))
          (((res.{t, u} j R).mapHomologicalComplex (.up ℤ)).obj P)) =
      (extD (q ((rings.{t, u} j).map b))).map ((resD.{t, u} j S).map (computation (p a) P)) ≫
      (extD (q ((rings.{t, u} j).map b))).map ((res.{t, u} j S).mapDerivedCategoryFactors.hom.app
          (((ext.{t, u} (Z := X) (p a)).mapHomologicalComplex (.up ℤ)).obj P)) ≫
      (extD (q ((rings.{t, u} j).map b))).map (DerivedCategory.Q.map ((d.chain a).hom.app P)) := by
    simp only [← Functor.map_comp]
    rw [hrep a P hP hf]
  rw [reassoc_of% hA]
  have hB : (d.derived b).hom.app ((extD (p a)).obj (DerivedCategory.Q.obj P)) ≫
      (extD (q ((rings.{t, u} j).map b))).map ((resD.{t, u} j S).map (computation (p a) P)) =
      (resD.{t, u} j T).map ((extD (p b)).map (computation (p a) P)) ≫
      (d.derived b).hom.app (DerivedCategory.Q.obj
        (((ext.{t, u} (Z := X) (p a)).mapHomologicalComplex (.up ℤ)).obj P)) :=
    ((d.derived b).hom.naturality _).symm
  rw [reassoc_of% hB, reassoc_of% (computation_naturality (q ((rings.{t, u} j).map b))
    ((d.chain a).hom.app P)), reassoc_of% (hrep b _ hK hF)]
  simp only [Functor.map_comp]

/-- The termwise form of the composition square: both cochain comparisons agree degreewise by
the ordinary composition square.
Source: Stacks 06YY, 0D6D (auxiliary; not a blueprint node). -/
private theorem composition_model_chain
    {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    {p : Presentations.{t, u} X} {q : Presentations.{t, u} Y}
    (n : Normalization.{t + 1, t, max u (t + 1), max (u + 1) (t + 2)}
      (C := X.ProEt) (J := topology X) (hD := derived.{t, u} X) @p)
    (m : Normalization.{t + 1, t, max u (t + 1), max (u + 1) (t + 2)}
      (C := Y.ProEt) (J := topology Y) (hD := derived.{t, u} Y) @q)
    (d : Comparison.{t, u} j @p @q) (hdegree : d.degree)
    (hordinary : ∀ {R S T : Sheaf (topology X) CommRingCat.{max u (t + 1)}}
    (a : R ⟶ S) (b : S ⟶ T) (M : Mods.{t, u} R),
    (res.{t, u} j T).map ((n.ordinary a b).hom.app M) ≫
        (d.ordinary (a ≫ b)).hom.app M =
      (d.ordinary b).hom.app ((ext.{t, u} (Z := X) (p a)).obj M) ≫
        (ext.{t, u} (Z := Y) (q ((rings.{t, u} j).map b))).map ((d.ordinary a).hom.app M) ≫
        (m.ordinary ((rings.{t, u} j).map a) ((rings.{t, u} j).map b)).hom.app
          ((res.{t, u} j R).obj M) ≫
        eqToHom (congrArg (fun f ↦ (ext.{t, u} (Z := Y) (q f)).obj ((res.{t, u} j R).obj M))
          ((rings.{t, u} j).map_comp a b).symm))
    {R S T : Sheaf (topology X) CommRingCat.{max u (t + 1)}}
    (a : R ⟶ S) (b : S ⟶ T) (P : CochainComplex (Mods.{t, u} R) ℤ) :
    ((res.{t, u} j T).mapHomologicalComplex (.up ℤ)).map
        ((Functor.mapHomologicalComplexCompIso (n.ordinary a b) (.up ℤ)).hom.app P) ≫
        (d.chain (a ≫ b)).hom.app P =
      ((d.chain b).hom.app (((ext.{t, u} (Z := X) (p a)).mapHomologicalComplex (.up ℤ)).obj P) ≫
        ((ext.{t, u} (Z := Y) (q ((rings.{t, u} j).map b))).mapHomologicalComplex (.up ℤ)).map
          ((d.chain a).hom.app P) ≫
        (Functor.mapHomologicalComplexCompIso
          (m.ordinary ((rings.{t, u} j).map a) ((rings.{t, u} j).map b)) (.up ℤ)).hom.app
          (((res.{t, u} j R).mapHomologicalComplex (.up ℤ)).obj P)) ≫
        eqToHom (congrArg (fun f ↦ ((ext.{t, u} (Z := Y) (q f)).mapHomologicalComplex (.up ℤ)).obj
          (((res.{t, u} j R).mapHomologicalComplex (.up ℤ)).obj P))
          ((rings.{t, u} j).map_comp a b).symm) := by
  refine HomologicalComplex.hom_ext _ _ (fun k ↦ ?_)
  simp only [HomologicalComplex.comp_f, hdegree (a ≫ b) P k,
    hdegree b _ k, Functor.mapHomologicalComplex_map_f, hdegree a P k,
    mapHomologicalComplexCompIso_hom_app_f, eqToHom_refl, Category.comp_id]
  have h := hordinary a b (P.X k)
  simp only [eqToHom_refl, Category.comp_id] at h
  exact h

set_option maxHeartbeats 400000 in
-- Rewriting in composites of derived functors requires large instance-level unification.
/-- On a flat-term K-flat complex whose restriction is also flat-term K-flat,
the normalized derived scalar-composition square follows from the ordinary square.
Source: Stacks Project, sites-cohomology.tex, Tags 06YY and 0D6D, the composition
part of the representative calculation in the parent coherence node.
(blueprint: lem-pur-clopen-scalar-composition-model).

Proof: write E_a for ordinary extension and c_a for the canonical computation.
Postcompose both paths by the image of the restriction factorization at P followed
by c_(a_i b_i) on the restricted P. These are isomorphisms by computed. On the
left, use the ambient normalization representative and the comparison representative
for ab. On the right, use naturality to move c_a past the comparison for b, then
apply the comparison representatives for b at E_a P and for a at P. Extended gives
flat terms and K-flatness for E_a P and its restriction, so all representative
identities used are available. Apply the component normalization representative
at the restricted P. Naturality of the restriction factorization identifies its
images of cochain morphisms. After functoriality and reassociation, both expressions
are the same computation morphisms followed by Q of the two cochain maps induced
by the ordinary composition square. Their degree-k components agree by hordinary
at P.X k and hdegree. Thus the cochain maps agree. Functor.map_comp transports
identify the actual same ring map and act by the corresponding equality maps on
complexes. Cancel the postcomposed isomorphisms. There is no localization-density
step in this lemma: P is fixed. All computations also hold for zero rings and
zero complexes, and no flatness of either coefficient map is assumed. -/
theorem clopen_scalar_composition_model
    {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    {p : Presentations.{t, u} X} {q : Presentations.{t, u} Y}
    (n : Normalization.{t + 1, t, max u (t + 1), max (u + 1) (t + 2)}
      (C := X.ProEt) (J := topology X) (hD := derived.{t, u} X) @p)
    (m : Normalization.{t + 1, t, max u (t + 1), max (u + 1) (t + 2)}
      (C := Y.ProEt) (J := topology Y) (hD := derived.{t, u} Y) @q)
    (d : Comparison.{t, u} j @p @q)
    (hdegree : d.degree) (hrep : d.representative)
    (hcomputed : d.computed) (hextended : d.extended)
    (hordinary : ∀ {R S T : Sheaf (topology X) CommRingCat.{max u (t + 1)}}
    (a : R ⟶ S) (b : S ⟶ T) (M : Mods.{t, u} R),
    (res.{t, u} j T).map ((n.ordinary a b).hom.app M) ≫
        (d.ordinary (a ≫ b)).hom.app M =
      (d.ordinary b).hom.app ((ext.{t, u} (Z := X) (p a)).obj M) ≫
        (ext.{t, u} (Z := Y) (q ((rings.{t, u} j).map b))).map ((d.ordinary a).hom.app M) ≫
        (m.ordinary ((rings.{t, u} j).map a) ((rings.{t, u} j).map b)).hom.app ((res.{t, u} j R).obj
          M) ≫
        eqToHom (congrArg (fun f ↦ (ext.{t, u} (Z := Y) (q f)).obj ((res.{t, u} j R).obj M))
          ((rings.{t, u} j).map_comp a b).symm))
    {R S T : Sheaf (topology X) CommRingCat.{max u (t + 1)}}
    (a : R ⟶ S) (b : S ⟶ T)
    (P : CochainComplex (Mods.{t, u} R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients.{t + 1, t, max u (t + 1)} (R := R) P)
    (hf : ∀ k : ℤ, IsFlatOnSite.{t + 1, t, max u (t + 1), max u (t + 1)} (J := topology X) (R :=
      R) (P.X k))
    (hiP : CochainComplex.IsKFlatIndependentCoefficients.{t + 1, t, max u (t + 1)} (R :=
      (rings.{t, u} j).obj R)
      (((res.{t, u} j R).mapHomologicalComplex (.up ℤ)).obj P))
    (hif : ∀ k : ℤ, IsFlatOnSite.{t + 1, t, max u (t + 1), max u (t + 1)} (J := topology Y) (R :=
      (rings.{t, u} j).obj R)
      ((res.{t, u} j R).obj (P.X k))) :
    (resD.{t, u} j T).map ((n.derived a b).hom.app (DerivedCategory.Q.obj P)) ≫
        (d.derived (a ≫ b)).hom.app (DerivedCategory.Q.obj P) =
      (d.derived b).hom.app ((extD.{t, u} (Z := X) (p a)).obj (DerivedCategory.Q.obj P)) ≫
        (extD.{t, u} (Z := Y) (q ((rings.{t, u} j).map b))).map ((d.derived a).hom.app
          (DerivedCategory.Q.obj P)) ≫
        (m.derived ((rings.{t, u} j).map a) ((rings.{t, u} j).map b)).hom.app ((resD.{t, u} j R).obj
          (DerivedCategory.Q.obj P)) ≫
        eqToHom (congrArg (fun f ↦ (extD.{t, u} (Z := Y) (q f)).obj ((resD.{t, u} j R).obj
          (DerivedCategory.Q.obj P)))
          ((rings.{t, u} j).map_comp a b).symm) := by
  have hc := (hcomputed (a ≫ b) P hP hf).2
  obtain ⟨hK, hF, -, -⟩ := hextended a P hP hf
  apply (cancel_mono ((extD (q ((rings.{t, u} j).map (a ≫ b)))).map
    ((res.{t, u} j R).mapDerivedCategoryFactors.hom.app P) ≫
    computation (q ((rings.{t, u} j).map (a ≫ b)))
      (((res.{t, u} j R).mapHomologicalComplex (.up ℤ)).obj P))).1
  simp only [Category.assoc]
  rw [hrep (a ≫ b) P hP hf, ← Functor.map_comp_assoc,
    normalization_derived_hom_app_comp_computation n a b P hP hf]
  simp only [Functor.map_comp, Category.assoc]
  erw [Functor.mapDerivedCategoryFactors_hom_naturality_assoc]
  rw [eqToHom_comp_extD_map_comp_computation q ((rings.{t, u} j).map_comp a b).symm
    (((res.{t, u} j R).mapHomologicalComplex (.up ℤ)).obj P)
    ((res.{t, u} j R).mapDerivedCategoryFactors.hom.app P),
    reassoc_of% (composition_model_right j m d hrep a b P hP hf hiP hif hK hF),
    ← Functor.map_comp DerivedCategory.Q (((res.{t, u} j T).mapHomologicalComplex (.up ℤ)).map _),
    composition_model_chain j n m d hdegree hordinary a b P]
  simp only [Functor.map_comp]

end AlgebraicGeometry.Scheme.ProEt.ClopenScalar
