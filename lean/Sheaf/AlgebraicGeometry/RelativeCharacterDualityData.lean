module

public import Sheaf.AlgebraicGeometry.RelativeTorus
public import Sheaf.AlgebraicGeometry.RelativeSplitTorusMatrixSheaf
public import WeilConjectures.AlgebraicGeometry.Sites.Gm
public import WeilConjectures.AlgebraicGeometry.Sites.UpperStarSections
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-! # Interfaces for relative character duality

Source: Lan, §3.1.1, Definitions 3.1.1.1, 3.1.1.4--5 and Lemma 3.1.1.6;
Milne, Algebraic Groups, §12 (blueprint: def-sfb-relative-character-duality-data).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.RelativeCharacter

/-- Finite free constant additive sheaf, including rank zero. Source: Lan, §3.1.1
(blueprint: def-sfb-relative-character-duality-data). -/
def free (S : Scheme.{u}) (r : ℕ) : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (constantSheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} (Fin r → ℤ)))

/-- Lattices are etale locally finite free, with variable rank. Source: Lan, §3.1.1
(blueprint: def-sfb-relative-character-duality-data). -/
def IsLattice {S : Scheme.{u}} (M : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) : Prop :=
  ∃ (I : Type u) (U : I → S.Etale) (r : I → ℕ),
    (⋃ i, (Set.range (fun x : (U i).left ↦ (U i).hom x) : Set S)) = Set.univ ∧
    ∀ i, Nonempty ((Etale.upperStar AddCommGrpCat.{u + 1} (U i).hom).obj M ≅
      free (U i).left (r i))

/-- The full category of etale lattices. Source: Lan, §3.1.1
(blueprint: def-sfb-relative-character-duality-data). -/
abbrev Lattice (S : Scheme.{u}) :=
  ObjectProperty.FullSubcategory (IsLattice (S := S))

/-- The full category of commutative relative tori, using the existing fppf-local
predicate. Source: Lan, §3.1.1 (blueprint: def-sfb-relative-character-duality-data). -/
abbrev Torus (S : Scheme.{u}) :=
  ObjectProperty.FullSubcategory (fun P : CommGrp (Over S) ↦ IsRelativeTorus P.X)

/-- Group scheme pullback is the existing pullback functor on group objects.
Source: Stacks, Tag 01JX (blueprint: def-sfb-relative-character-duality-data). -/
abbrev change {S T : Scheme.{u}} (f : T ⟶ S) := (Over.pullback f).mapCommGrp

/-- Canonical iterated pullback comparison. Source: Stacks, Tag 01JX
(blueprint: def-sfb-relative-character-duality-data). -/
def changeComp {S T V : Scheme.{u}} (a : V ⟶ T) (b : T ⟶ S) :
    change (a ≫ b) ≅ change b ⋙ change a :=
  Functor.mapCommGrpNatIso (Over.pullbackComp a b) ≪≫ Functor.mapCommGrpCompIso

/-- Pullback of a functional to the units sheaf, using the canonical units comparison,
which need not be invertible. Source: Lan, §3.1.1; Stacks, Tag 03P2
(blueprint: def-sfb-relative-character-duality-data). -/
def functionalChange {S : Scheme.{u}} (M : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})
    {T V : Over S} (a : V ⟶ T)
    (h : (Etale.upperStar AddCommGrpCat.{u + 1} T.hom).obj M ⟶ T.left.gmSheaf) :
    (Etale.upperStar AddCommGrpCat.{u + 1} V.hom).obj M ⟶ V.left.gmSheaf :=
  (Etale.upperStarComp AddCommGrpCat.{u + 1} a.left T.hom V.hom a.w.symm).hom.app M ≫
    (Etale.upperStar AddCommGrpCat.{u + 1} a.left).map h ≫
    Scheme.upperStarGmSheafToGmSheaf a.left

/-- Canonical base change of the split Laurent model. Source: Stacks, Tag 022U
(blueprint: def-sfb-relative-character-duality-data). -/
def splitChange {S T : Scheme.{u}} (f : T ⟶ S) (r : ℕ) :
    (change f).obj (RelativeSplitTorus.model S r) ≅ RelativeSplitTorus.model T r :=
  ((changeComp f (specULiftZIsTerminal.from S)).app
      (RelativeSplitTorus.integerModel r)).symm ≪≫
    eqToIso (congrArg (fun a ↦ (change a).obj (RelativeSplitTorus.integerModel r))
      (specULiftZIsTerminal.hom_ext (f ≫ specULiftZIsTerminal.from S)
        (specULiftZIsTerminal.from T)))

/-- Characters over a test scheme, with their pointwise commutative group structure.
Source: Lan, Definition 3.1.1.4 (blueprint: def-sfb-relative-character-duality-data). -/
abbrev Characters {S : Scheme.{u}} (P : CommGrp (Over S)) (T : Over S) :=
  ((change T.hom).obj P).toGrp ⟶ (RelativeSplitTorus.model T.left 1).toGrp

/-- Character restriction uses canonical pullback comparisons. Source: Lan, §3.1.1
(blueprint: def-sfb-relative-character-duality-data). -/
def characterChange {S : Scheme.{u}} (P : CommGrp (Over S))
    {T V : Over S} (a : V ⟶ T) (χ : Characters P T) : Characters P V :=
  ((CommGrp.forget₂Grp _).mapIso
    (eqToIso (congrArg (fun f ↦ (change f).obj P) a.w.symm) ≪≫
      (changeComp a.left T.hom).app P)).hom ≫
    (Over.pullback a.left).mapGrp.map χ ≫
    ((CommGrp.forget₂Grp _).mapIso (splitChange a.left 1)).hom

/-- The value of a character on a point as a global function; the function is a unit
because it is the pullback of the Laurent coordinate. Source: Stacks, Tag 022U
(blueprint: def-sfb-relative-character-duality-data). -/
def value {S : Scheme.{u}} (P : CommGrp (Over S)) (T : Over S)
    (χ : Characters P T) (x : T ⟶ P.X) : Γ(T.left, ⊤) :=
  ((((Over.mapPullbackAdj T.hom).homEquiv (Over.mk (𝟙 T.left)) P.X) x ≫
    χ.hom.hom).left).appTop (RelativeSplitTorus.coordinate T.left 1 0)

/-- Stability hypotheses used only to form the canonical pullback functors. These
are conclusions, not assumptions, of reconstruction. Source: Lan, §3.1.1
(blueprint: def-sfb-relative-character-duality-data). -/
structure Stable : Prop where
  torus : ∀ {S T : Scheme.{u}} (f : T ⟶ S) (P : Torus S),
    IsRelativeTorus ((change f).obj P.obj).X
  lattice : ∀ {S T : Scheme.{u}} (f : T ⟶ S) (M : Lattice S),
    IsLattice ((Etale.upperStar AddCommGrpCat.{u + 1} f).obj M.obj)

/-- Actual group-scheme base change restricted to tori. Source: Stacks, Tag 01JX
(blueprint: def-sfb-relative-character-duality-data). -/
def torusPull (h : Stable.{u}) {S T : Scheme.{u}} (f : T ⟶ S) : Torus S ⥤ Torus T where
  obj P := ⟨(change f).obj P.obj, h.torus f P⟩
  map a := ObjectProperty.homMk ((change f).map a.hom)

/-- Ordinary etale inverse image restricted to lattices. Source: Lan, §3.1.1
(blueprint: def-sfb-relative-character-duality-data). -/
def latticePull (h : Stable.{u}) {S T : Scheme.{u}} (f : T ⟶ S) :
    Lattice S ⥤ Lattice T where
  obj M := ⟨(Etale.upperStar AddCommGrpCat.{u + 1} f).obj M.obj, h.lattice f M⟩
  map a := ObjectProperty.homMk ((Etale.upperStar AddCommGrpCat.{u + 1} f).map a.hom)

/-- Iterated torus pullback, with the canonical scheme pullback comparison.
Source: Stacks, Tag 01JX (blueprint: def-sfb-relative-character-duality-data). -/
def torusPullComp (h : Stable.{u}) {S T V : Scheme.{u}} (a : V ⟶ T) (b : T ⟶ S) :
    torusPull h (a ≫ b) ≅ torusPull h b ⋙ torusPull h a :=
  NatIso.ofComponents (fun P ↦ ObjectProperty.isoMk _ ((changeComp a b).app P.obj))
    (fun _ ↦ ObjectProperty.hom_ext _ ((changeComp a b).hom.naturality _))

/-- Iterated lattice pullback, with the ordinary inverse-image comparison.
Source: Stacks, Tag 03P2 (blueprint: def-sfb-relative-character-duality-data). -/
def latticePullComp (h : Stable.{u}) {S T V : Scheme.{u}} (a : V ⟶ T) (b : T ⟶ S) :
    latticePull h (a ≫ b) ≅ latticePull h b ⋙ latticePull h a :=
  NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _
      ((Etale.upperStarComp AddCommGrpCat.{u + 1} a b).app M.obj))
    (fun _ ↦ ObjectProperty.hom_ext _
      ((Etale.upperStarComp AddCommGrpCat.{u + 1} a b).hom.naturality _))

/-- Identity torus pullback. Source: Stacks, Tag 01JX
(blueprint: def-sfb-relative-character-duality-data). -/
def torusPullId (h : Stable.{u}) (S : Scheme.{u}) : torusPull h (𝟙 S) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun P ↦ ObjectProperty.isoMk _
    ((Functor.mapCommGrpNatIso Over.pullbackId ≪≫ Functor.mapCommGrpIdIso).app P.obj))
    (fun _ ↦ ObjectProperty.hom_ext _
      ((Functor.mapCommGrpNatIso Over.pullbackId ≪≫ Functor.mapCommGrpIdIso).hom.naturality _))

/-- Identity lattice pullback. Source: Stacks, Tag 03P2
(blueprint: def-sfb-relative-character-duality-data). -/
def latticePullId (h : Stable.{u}) (S : Scheme.{u}) : latticePull h (𝟙 S) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _
    ((Etale.upperStarId AddCommGrpCat.{u + 1} S).app M.obj))
    (fun _ ↦ ObjectProperty.hom_ext _
      ((Etale.upperStarId AddCommGrpCat.{u + 1} S).hom.naturality _))

/-- Underlying character sheaf of an equivalence. Source: Lan, Lemma 3.1.1.6
(blueprint: def-sfb-relative-character-duality-data). -/
abbrev X {S : Scheme.{u}} (E : (Torus S)ᵒᵖ ≌ Lattice S) (P : Torus S) :=
  (E.functor.obj (op P)).obj

/-- Underlying reconstructed group of a quasi-inverse. Source: Lan, Lemma 3.1.1.6
(blueprint: def-sfb-relative-character-duality-data). -/
abbrev D {S : Scheme.{u}} (E : (Torus S)ᵒᵖ ≌ Lattice S) (M : Lattice S) :=
  (E.inverse.obj M).unop.obj

/-- Pullback of a section to the identity object over its domain. Source: Stacks, Tag 03P2
(blueprint: def-sfb-relative-character-duality-data). -/
def sectionOver {S : Scheme.{u}} (M : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})
    (U : S.Etale) (m : M.obj.obj (op U)) :
    ((Etale.upperStar AddCommGrpCat.{u + 1} U.hom).obj M).obj.obj
      (op (Scheme.Etale.mk (𝟙 U.left))) :=
  Etale.pullSection U.hom M (𝟙 U.left) (Category.id_comp U.hom |>.trans
    (Category.id_comp U.hom).symm) m

/-- Evaluation of a sheaf functional at a section. Source: Lan, §3.1.1
(blueprint: def-sfb-relative-character-duality-data). -/
def functionalValue {S : Scheme.{u}} (M : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})
    (U : S.Etale)
    (h : (Etale.upperStar AddCommGrpCat.{u + 1} U.hom).obj M ⟶ U.left.gmSheaf)
    (m : M.obj.obj (op U)) : Γ(U.left, ⊤) :=
  ↑(Additive.toMul ((h.hom.app (op (Scheme.Etale.mk (𝟙 U.left))))
    (sectionOver M U m)).down : Γ(U.left, ⊤)ˣ)

/-- A relative character reconstruction datum. Each field specifies part of the
construction, rather than assuming its existence. The character and point equivalences
are pinned by restriction, precomposition and both evaluation maps. Base-change
comparisons are natural, and the dual comparison is the mate of the character comparison.
Source: Lan, §3.1.1, Definitions 3.1.1.1, 3.1.1.4--5 and Lemma 3.1.1.6;
Milne, §12; Stacks, Tag 022U (blueprint: def-sfb-relative-character-duality-data). -/
structure Data where
  stable : Stable.{u}
  equivalence : ∀ S : Scheme.{u}, (Torus S)ᵒᵖ ≌ Lattice S
  characters : ∀ (S : Scheme.{u}) (P : Torus S) (U : S.Etale),
    (X (equivalence S) P).obj.obj (op U) ≃+
      Additive (Characters P.obj (Over.mk U.hom))
  represent : ∀ (S : Scheme.{u}) (M : Lattice S) (T : Over S),
    Additive (T ⟶ (D (equivalence S) M).X) ≃+
      ((Etale.upperStar AddCommGrpCat.{u + 1} T.hom).obj M.obj ⟶ T.left.gmSheaf)
  character_baseChange : ∀ {S T : Scheme.{u}} (f : T ⟶ S),
    (torusPull stable f).op ⋙ (equivalence T).functor ≅
      (equivalence S).functor ⋙ latticePull stable f
  dual_baseChange : ∀ {S T : Scheme.{u}} (f : T ⟶ S),
    (equivalence S).inverse ⋙ (torusPull stable f).op ≅
      latticePull stable f ⋙ (equivalence T).inverse

/-- The characters restrict clause of relative character reconstruction.
Source: Lan, §3.1.1, Lemma 3.1.1.6; Milne, §12
(blueprint: def-sfb-relative-character-duality-data). -/
def characters_restrict (R : Data.{u}) : Prop :=
  ∀ (S : Scheme.{u}) (P : Torus S) (U V : S.Etale)
      (a : V ⟶ U) (χ : (X (R.equivalence S) P).obj.obj (op U)),
    (R.characters S P V ((X (R.equivalence S) P).obj.map a.op χ)).toMul =
      characterChange P.obj ((Scheme.Etale.forget S).map a) (R.characters S P U χ).toMul

/-- The characters map clause of relative character reconstruction.
Source: Lan, §3.1.1, Lemma 3.1.1.6; Milne, §12
(blueprint: def-sfb-relative-character-duality-data). -/
def characters_map (R : Data.{u}) : Prop :=
  ∀ (S : Scheme.{u}) (P Q : Torus S) (a : P ⟶ Q)
      (U : S.Etale) (χ : (X (R.equivalence S) Q).obj.obj (op U)),
    (R.characters S P U
      (((R.equivalence S).functor.map a.op).hom.hom.app (op U) χ)).toMul =
      ((change U.hom).map a.hom).hom ≫ (R.characters S Q U χ).toMul

/-- The represent restrict clause of relative character reconstruction.
Source: Lan, §3.1.1, Lemma 3.1.1.6; Milne, §12
(blueprint: def-sfb-relative-character-duality-data). -/
def represent_restrict (R : Data.{u}) : Prop :=
  ∀ (S : Scheme.{u}) (M : Lattice S) (T V : Over S)
      (a : V ⟶ T) (x : T ⟶ (D (R.equivalence S) M).X),
    R.represent S M V (Additive.ofMul (a ≫ x)) =
      functionalChange M.obj a (R.represent S M T (Additive.ofMul x))

/-- The represent map clause of relative character reconstruction.
Source: Lan, §3.1.1, Lemma 3.1.1.6; Milne, §12
(blueprint: def-sfb-relative-character-duality-data). -/
def represent_map (R : Data.{u}) : Prop :=
  ∀ (S : Scheme.{u}) (M N : Lattice S) (a : M ⟶ N)
      (T : Over S) (x : T ⟶ (D (R.equivalence S) N).X),
    R.represent S M T (Additive.ofMul
      (x ≫ ((R.equivalence S).inverse.map a).unop.hom.hom.hom.hom)) =
      (Etale.upperStar AddCommGrpCat.{u + 1} T.hom).map a.hom ≫
        R.represent S N T (Additive.ofMul x)

/-- The counit evaluation clause of relative character reconstruction.
Source: Lan, §3.1.1, Lemma 3.1.1.6; Milne, §12
(blueprint: def-sfb-relative-character-duality-data). -/
def counit_evaluation (R : Data.{u}) : Prop :=
  ∀ (S : Scheme.{u}) (M : Lattice S) (U : S.Etale)
      (m : M.obj.obj.obj (op U)) (x : Over.mk U.hom ⟶ (D (R.equivalence S) M).X),
    value (D (R.equivalence S) M) (Over.mk U.hom)
      (R.characters S ((R.equivalence S).inverse.obj M).unop U
        (((R.equivalence S).counitIso.inv.app M).hom.hom.app (op U) m)).toMul x =
      functionalValue M.obj U (R.represent S M (Over.mk U.hom) (Additive.ofMul x)) m

/-- The unit evaluation clause of relative character reconstruction.
Source: Lan, §3.1.1, Lemma 3.1.1.6; Milne, §12
(blueprint: def-sfb-relative-character-duality-data). -/
def unit_evaluation (R : Data.{u}) : Prop :=
  ∀ (S : Scheme.{u}) (P : Torus S) (U : S.Etale)
      (χ : (X (R.equivalence S) P).obj.obj (op U)) (x : Over.mk U.hom ⟶ P.obj.X),
    functionalValue (X (R.equivalence S) P) U
      (R.represent S ((R.equivalence S).functor.obj (op P)) (Over.mk U.hom)
        (Additive.ofMul (x ≫
          ((R.equivalence S).unitIso.inv.app (op P)).unop.hom.hom.hom.hom))) χ =
      value P.obj (Over.mk U.hom) (R.characters S P U χ).toMul x

/-- The character baseChange id clause of relative character reconstruction.
Source: Lan, §3.1.1, Lemma 3.1.1.6; Milne, §12
(blueprint: def-sfb-relative-character-duality-data). -/
def character_baseChange_id (R : Data.{u}) : Prop :=
  ∀ (S : Scheme.{u}) (P : Torus S),
    (R.equivalence S).functor.map (((torusPullId R.stable S).hom.app P).op) ≫
      (R.character_baseChange (𝟙 S)).hom.app (op P) ≫
      (latticePullId R.stable S).hom.app ((R.equivalence S).functor.obj (op P)) = 𝟙 _

/-- The character baseChange comp clause of relative character reconstruction.
Source: Lan, §3.1.1, Lemma 3.1.1.6; Milne, §12
(blueprint: def-sfb-relative-character-duality-data). -/
def character_baseChange_comp (R : Data.{u}) : Prop :=
  ∀ {S T V : Scheme.{u}} (a : V ⟶ T) (b : T ⟶ S)
      (P : Torus S),
    (R.equivalence V).functor.map (((torusPullComp R.stable a b).hom.app P).op) ≫
      (R.character_baseChange (a ≫ b)).hom.app (op P) ≫
      (latticePullComp R.stable a b).hom.app ((R.equivalence S).functor.obj (op P)) =
      (R.character_baseChange a).hom.app (op ((torusPull R.stable b).obj P)) ≫
        (latticePull R.stable a).map ((R.character_baseChange b).hom.app (op P))

/-- The baseChange mate clause of relative character reconstruction.
Source: Lan, §3.1.1, Lemma 3.1.1.6; Milne, §12
(blueprint: def-sfb-relative-character-duality-data). -/
def baseChange_mate (R : Data.{u}) : Prop :=
  ∀ {S T : Scheme.{u}} (f : T ⟶ S) (M : Lattice S),
    (R.equivalence T).functor.map ((R.dual_baseChange f).hom.app M) ≫
        (R.equivalence T).counitIso.hom.app ((latticePull R.stable f).obj M) =
      (R.character_baseChange f).hom.app ((R.equivalence S).inverse.obj M) ≫
        (latticePull R.stable f).map ((R.equivalence S).counitIso.hom.app M)

/-- The character baseChange evaluation clause of relative character reconstruction.
Source: Lan, §3.1.1, Lemma 3.1.1.6; Milne, §12
(blueprint: def-sfb-relative-character-duality-data). -/
def character_baseChange_evaluation (R : Data.{u}) : Prop :=
  ∀ {S T : Scheme.{u}} (f : T ⟶ S)
      (P : Torus S) (U : S.Etale) (V : T.Etale) (k : V.left ⟶ U.left)
      (hk : k ≫ U.hom = V.hom ≫ f) (χ : (X (R.equivalence S) P).obj.obj (op U))
      (x : Over.mk V.hom ⟶ ((change f).obj P.obj).X),
    value ((change f).obj P.obj) (Over.mk V.hom)
      (R.characters T ((torusPull R.stable f).obj P) V
        (((R.character_baseChange f).inv.app (op P)).hom.hom.app (op V)
          (Etale.pullSection f (X (R.equivalence S) P) k hk χ))).toMul x =
      value P.obj (Over.mk (V.hom ≫ f))
        (characterChange P.obj (Over.homMk k hk) (R.characters S P U χ).toMul)
        ((Over.map f).map x ≫ (Over.mapPullbackAdj f).counit.app P.obj.X)

/-- The local split clause of relative character reconstruction.
Source: Lan, §3.1.1, Lemma 3.1.1.6; Milne, §12
(blueprint: def-sfb-relative-character-duality-data). -/
def local_split (R : Data.{u}) : Prop :=
  ∀ (S T : Scheme.{u}) (f : T ⟶ S) (M : Lattice S) (r : ℕ),
    Nonempty ((Etale.upperStar AddCommGrpCat.{u + 1} f).obj M.obj ≅ free T r) →
      Nonempty ((change f).obj (D (R.equivalence S) M) ≅ RelativeSplitTorus.model T r)

/-- The smooth clause of relative character reconstruction.
Source: Lan, §3.1.1, Lemma 3.1.1.6; Milne, §12
(blueprint: def-sfb-relative-character-duality-data). -/
def smooth (R : Data.{u}) : Prop :=
  ∀ (S : Scheme.{u}) (M : Lattice S), Smooth (D (R.equivalence S) M).X.hom

/-- The affine clause of relative character reconstruction.
Source: Lan, §3.1.1, Lemma 3.1.1.6; Milne, §12
(blueprint: def-sfb-relative-character-duality-data). -/
def affine (R : Data.{u}) : Prop :=
  ∀ (S : Scheme.{u}) (M : Lattice S), IsAffineHom (D (R.equivalence S) M).X.hom

/-- The flat clause of relative character reconstruction.
Source: Lan, §3.1.1, Lemma 3.1.1.6; Milne, §12
(blueprint: def-sfb-relative-character-duality-data). -/
def flat (R : Data.{u}) : Prop :=
  ∀ (S : Scheme.{u}) (M : Lattice S), Flat (D (R.equivalence S) M).X.hom

/-- The surjective clause of relative character reconstruction.
Source: Lan, §3.1.1, Lemma 3.1.1.6; Milne, §12
(blueprint: def-sfb-relative-character-duality-data). -/
def surjective (R : Data.{u}) : Prop :=
  ∀ (S : Scheme.{u}) (M : Lattice S),
    Surjective (D (R.equivalence S) M).X.hom

/-- The finitePresentation clause of relative character reconstruction.
Source: Lan, §3.1.1, Lemma 3.1.1.6; Milne, §12
(blueprint: def-sfb-relative-character-duality-data). -/
def finitePresentation (R : Data.{u}) : Prop :=
  ∀ (S : Scheme.{u}) (M : Lattice S),
    LocallyOfFinitePresentation (D (R.equivalence S) M).X.hom ∧
      QuasiCompact (D (R.equivalence S) M).X.hom ∧ QuasiSeparated (D (R.equivalence S) M).X.hom

/-- The geometric fibre clause of relative character reconstruction.
Source: Lan, §3.1.1, Lemma 3.1.1.6; Milne, §12
(blueprint: def-sfb-relative-character-duality-data). -/
def geometric_fibre (R : Data.{u}) : Prop :=
  ∀ (S : Scheme.{u}) (M : Lattice S) (Ω : Type u)
      [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S),
    ∃ r : ℕ, Nonempty ((Etale.upperStar AddCommGrpCat.{u + 1} s).obj M.obj ≅
      free (Spec (.of Ω)) r) ∧
      Nonempty ((change s).obj (D (R.equivalence S) M) ≅
        RelativeSplitTorus.model (Spec (.of Ω)) r)

/-- All normalization and geometric clauses on the reconstruction data.
Source: Lan, §3.1.1, Lemma 3.1.1.6; Milne, §12
(blueprint: def-sfb-relative-character-duality-data). -/
def IsReconstruction (R : Data.{u}) : Prop :=
  characters_restrict R ∧
  characters_map R ∧
  represent_restrict R ∧
  represent_map R ∧
  counit_evaluation R ∧
  unit_evaluation R ∧
  character_baseChange_id R ∧
  character_baseChange_comp R ∧
  baseChange_mate R ∧
  character_baseChange_evaluation R ∧
  local_split R ∧
  smooth R ∧
  affine R ∧
  flat R ∧
  surjective R ∧
  finitePresentation R ∧
  geometric_fibre R

/-- Relative character reconstruction, with actual data and all its stated properties.
Source: Lan, §3.1.1, Lemma 3.1.1.6; Milne, §12
(blueprint: def-sfb-relative-character-duality-data). -/
structure Reconstruction where
  data : Data.{u}
  valid : IsReconstruction data

end AlgebraicGeometry.RelativeCharacter
