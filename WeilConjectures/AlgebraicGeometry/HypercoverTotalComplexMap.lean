/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.HypercoverTotalComplex

/-!
# Functoriality of the total complex of a hypercover

The total complex `Tot(U, L)` of `AlgebraicGeometry.SplitEtaleHypercover.totComplex` is
contravariantly functorial in refinements `V ⟶ U` of hypercovers and covariantly functorial in
maps of complexes `L ⟶ L'`, compatibly with the augmentation `Γ(X, L) ⟶ Tot(U, L)` and with
the maps `C(U, F) ⟶ Tot(U, L)`.
-/

@[expose] public section

universe u u'

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

namespace AlgebraicGeometry.SplitEtaleHypercover

variable {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
  {A : Type u'} [Category.{u + 1} A] [Abelian A]
  (L : CochainComplex (Sheaf X.smallEtaleTopology A) ℕ)

attribute [local instance] Abelian.hasFiniteBiproducts

section Refinement

variable {U V : SplitEtaleHypercover X} (f : V.simplicial ⟶ U.simplicial)

/-- Restriction of sections along a refinement in degree `p`. -/
noncomputable abbrev resMap (G : Sheaf X.smallEtaleTopology A) (p : ℕ) :
    G.obj.obj (op (U.simplicial _⦋p⦌)) ⟶ G.obj.obj (op (V.simplicial _⦋p⦌)) :=
  G.obj.map (f.app (op ⦋p⦌)).op

/-- The map of complexes of sections induced by a refinement. -/
noncomputable abbrev secMap (G : Sheaf X.smallEtaleTopology A) :
    U.secComplex G ⟶ V.secComplex G :=
  (AlgebraicTopology.alternatingCofaceMapComplex A).map
    (Functor.whiskerRight (NatTrans.rightOp f) G.obj)

lemma secMap_f (G : Sheaf X.smallEtaleTopology A) (p : ℕ) :
    (secMap f G).f p = resMap f G p := rfl

lemma dHor_resMap (p r : ℕ) :
    U.dHor L p r ≫ resMap f (L.X r) (p + 1) = resMap f (L.X r) p ≫ V.dHor L p r :=
  ((secMap f (L.X r)).comm p (p + 1)).symm

lemma dVert_resMap (p r : ℕ) :
    U.dVert L p r ≫ resMap f (L.X (r + 1)) p = resMap f (L.X r) p ≫ V.dVert L p r :=
  ((L.d r (r + 1)).hom.naturality _).symm

/-- The map of total complexes induced by a refinement, in degree `n`. -/
noncomputable def totMapF (n : ℕ) : U.totObj L n ⟶ V.totObj L n :=
  biproduct.map fun x ↦ resMap f (L.X x.1.2) x.1.1

lemma totι_totMapF (p r n : ℕ) (h : p + r = n) :
    U.totι L p r n h ≫ totMapF L f n = resMap f (L.X r) p ≫ V.totι L p r n h :=
  by rw [totι, totι, totMapF, biproduct.ι_map]

/-- The map of total complexes induced by a refinement. -/
noncomputable def totMap : U.totComplex L ⟶ V.totComplex L :=
  CochainComplex.ofHom (totMapF L f) fun n ↦ by
    rw [totComplex_d, totComplex_d]
    apply totObj_hom_ext
    intro p r h
    rw [← Category.assoc, totι_totMapF, Category.assoc, totι_totD, ← Category.assoc, totι_totD]
    simp only [Preadditive.add_comp, Preadditive.comp_add, Preadditive.zsmul_comp,
      Preadditive.comp_zsmul, Category.assoc, totι_totMapF]
    rw [← Category.assoc (U.dHor L p r), dHor_resMap, ← Category.assoc (U.dVert L p r),
      dVert_resMap]
    simp only [Category.assoc]

lemma totMap_f (n : ℕ) : (totMap L f).f n = totMapF L f n := rfl

lemma totAug_totMap : U.totAug L ≫ totMap L f = V.totAug L := by
  ext n : 1
  change (U.resTop (L.X n) 0 ≫ U.totι L 0 n n _) ≫ totMapF L f n =
    V.resTop (L.X n) 0 ≫ V.totι L 0 n n _
  rw [Category.assoc, totι_totMapF, ← Category.assoc]
  congr 1
  rw [← Functor.map_comp, ← op_comp]
  congr 2
  exact terminal.hom_ext _ _

lemma totRow_totMap {F : Sheaf X.smallEtaleTopology A} (ι : F ⟶ L.X 0)
    (hι : ι ≫ L.d 0 1 = 0) :
    U.totRow ι hι ≫ totMap L f = secMap f F ≫ V.totRow ι hι := by
  ext n : 1
  change (ι.hom.app _ ≫ U.totι L n 0 n _) ≫ totMapF L f n =
    resMap f F n ≫ ι.hom.app _ ≫ V.totι L n 0 n _
  rw [Category.assoc, totι_totMapF, ← Category.assoc, ← Category.assoc]
  congr 1
  exact (ι.hom.naturality _).symm

end Refinement

section Complex

variable (U : SplitEtaleHypercover X) {L} {L' : CochainComplex (Sheaf X.smallEtaleTopology A) ℕ}
  (φ : L ⟶ L')

/-- The map of total complexes induced by a map of complexes, in degree `n`. -/
noncomputable def totMapLF (n : ℕ) : U.totObj L n ⟶ U.totObj L' n :=
  biproduct.map fun x ↦ (φ.f x.1.2).hom.app (op (U.simplicial _⦋x.1.1⦌))

lemma totι_totMapLF (p r n : ℕ) (h : p + r = n) :
    U.totι L p r n h ≫ U.totMapLF φ n =
      (φ.f r).hom.app (op (U.simplicial _⦋p⦌)) ≫ U.totι L' p r n h :=
  by rw [totι, totι, totMapLF, biproduct.ι_map]

lemma dHor_comp_app (p r : ℕ) :
    U.dHor L p r ≫ (φ.f r).hom.app (op (U.simplicial _⦋p + 1⦌)) =
      (φ.f r).hom.app (op (U.simplicial _⦋p⦌)) ≫ U.dHor L' p r :=
  (((AlgebraicTopology.alternatingCofaceMapComplex A).map
    (Functor.whiskerLeft U.simplicial.rightOp (φ.f r).hom)).comm p (p + 1)).symm

lemma dVert_comp_app (p r : ℕ) :
    U.dVert L p r ≫ (φ.f (r + 1)).hom.app (op (U.simplicial _⦋p⦌)) =
      (φ.f r).hom.app (op (U.simplicial _⦋p⦌)) ≫ U.dVert L' p r := by
  rw [← NatTrans.comp_app, ← NatTrans.comp_app]
  change ((L.d r (r + 1)) ≫ φ.f (r + 1)).hom.app _ = (φ.f r ≫ L'.d r (r + 1)).hom.app _
  rw [φ.comm]

/-- The map of total complexes induced by a map of complexes. -/
noncomputable def totMapL : U.totComplex L ⟶ U.totComplex L' :=
  CochainComplex.ofHom (U.totMapLF φ) fun n ↦ by
    rw [totComplex_d, totComplex_d]
    apply totObj_hom_ext
    intro p r h
    rw [← Category.assoc, totι_totMapLF, Category.assoc, totι_totD, ← Category.assoc, totι_totD]
    simp only [Preadditive.add_comp, Preadditive.comp_add, Preadditive.zsmul_comp,
      Preadditive.comp_zsmul, Category.assoc, totι_totMapLF]
    rw [← Category.assoc (U.dHor L p r), dHor_comp_app, ← Category.assoc (U.dVert L p r),
      dVert_comp_app]
    simp only [Category.assoc]

lemma totMapL_f (n : ℕ) : (U.totMapL φ).f n = U.totMapLF φ n := rfl

lemma totAug_totMapL :
    U.totAug L ≫ U.totMapL φ =
      (((sheafSections X.smallEtaleTopology A).obj (op (⊤_ X.Etale))).mapHomologicalComplex
        _).map φ ≫ U.totAug L' := by
  ext n : 1
  change (U.resTop (L.X n) 0 ≫ U.totι L 0 n n _) ≫ U.totMapLF φ n =
    (φ.f n).hom.app _ ≫ U.resTop (L'.X n) 0 ≫ U.totι L' 0 n n _
  rw [Category.assoc, totι_totMapLF, ← Category.assoc, ← Category.assoc]
  congr 1
  exact (φ.f n).hom.naturality _

lemma totRow_totMapL {F F' : Sheaf X.smallEtaleTopology A} (ι : F ⟶ L.X 0)
    (hι : ι ≫ L.d 0 1 = 0) (ι' : F' ⟶ L'.X 0) (hι' : ι' ≫ L'.d 0 1 = 0) (g : F ⟶ F')
    (hg : ι ≫ φ.f 0 = g ≫ ι') :
    U.totRow ι hι ≫ U.totMapL φ =
      (AlgebraicTopology.alternatingCofaceMapComplex A).map
        (Functor.whiskerLeft U.simplicial.rightOp g.hom) ≫ U.totRow ι' hι' := by
  ext n : 1
  change (ι.hom.app _ ≫ U.totι L n 0 n _) ≫ U.totMapLF φ n =
    g.hom.app _ ≫ ι'.hom.app _ ≫ U.totι L' n 0 n _
  rw [Category.assoc, totι_totMapLF, ← Category.assoc, ← Category.assoc]
  congr 1
  rw [← NatTrans.comp_app, ← NatTrans.comp_app]
  change (ι ≫ φ.f 0).hom.app _ = (g ≫ ι').hom.app _
  rw [hg]

end Complex

end AlgebraicGeometry.SplitEtaleHypercover
