module

public import Sheaf.CategoryTheory.SheafDgModuleLocalization
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
import Sheaf.CategoryTheory.Sites.InverseImageUnderlyingAdjunction
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TopologicalPullback
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal
import Mathlib.Topology.Sheaves.Functors

/-! # The underived sheaf dg pullback and pushforward Hom adjunction

Source: Stacks Project, sdga.tex, Tags 0FR8 and 0FRU, section-functoriality-dg.
(blueprint: lem-sfb-sheaf-dg-pushpull-hom).

The coefficient map is written in its adjoint form S → f_* T. The dg algebra map
is likewise written C → f_* B. The pullback below is an actual balanced coequalizer
of free B-modules on ordinary coefficient pullbacks. This equals the inverse-image
balanced tensor B ⊗_{f⁻¹C} f⁻¹N, without assuming any exactness.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Opposite TopologicalSpace

namespace CategoryTheory.SheafDg.Pushpull

variable {X Z : TopCat.{u}} (f : X ⟶ Z)
  (S : Z.Sheaf CommRingCat.{u}) (T : X.Sheaf CommRingCat.{u})
  (c : rings S ⟶ ((Opens.map f).sheafPushforwardContinuous RingCat.{u}
    (Opens.grothendieckTopology Z) (Opens.grothendieckTopology X)).obj (rings T))

/-- Ordinary coefficient direct image, with the action through c.
Source: Stacks, 03D6 (blueprint: lem-sfb-sheaf-dg-pushpull-hom). -/
abbrev coefficientPush :=
  SheafOfModules.pushforward.{u} (F := Opens.map f) (S := rings S) (R := rings T) c

/-- Existence of ordinary coefficient pullback: Mathlib's presheaf pullback followed by
sheafification (`SheafOfModules.PullbackConstruction.adjunction`) is a left adjoint on
spaces whose opens and coefficients lie in one universe.
Source: Stacks, 03D7 (blueprint: lem-sfb-sheaf-dg-pushpull-hom). -/
instance coefficientPushRightAdjoint : (coefficientPush f S T c).IsRightAdjoint :=
  inferInstance

/-- Ordinary pullback, canonically the sheafified O_X ⊗_{f⁻¹O_Z} f⁻¹(-).
Source: Stacks, 03D7 (blueprint: lem-sfb-sheaf-dg-pushpull-hom). -/
abbrev coefficientPull :=
  SheafOfModules.pullback.{u} (F := Opens.map f) (S := rings S) (R := rings T) c

/-- The ordinary module adjunction, including its fixed unit and counit.
Source: Stacks, 03D7 (blueprint: lem-sfb-sheaf-dg-pushpull-hom). -/
abbrev coefficientAdjunction : coefficientPull f S T c ⊣ coefficientPush f S T c :=
  SheafOfModules.pullbackPushforwardAdjunction
    (F := Opens.map f) (S := rings S) (R := rings T) c

/-- Pullback of the coefficient complex, degree by degree, without deriving it.
Source: Stacks, 0FRT (blueprint: lem-sfb-sheaf-dg-pushpull-hom). -/
abbrev pullComplex : Complex S ⥤ Complex T :=
  (coefficientPull f S T c).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Direct image of the coefficient complex, degree by degree.
Source: Stacks, 0FRT (blueprint: lem-sfb-sheaf-dg-pushpull-hom). -/
abbrev pushComplex : Complex T ⥤ Complex S :=
  (coefficientPush f S T c).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The image 1 ⊗ n of an original section in ordinary coefficient pullback.
Source: Stacks, 03D7 and 0FRU (blueprint: lem-sfb-sheaf-dg-pushpull-hom). -/
def pullSection (K : Complex S) (i : ℤ) (V : (Opens Z)ᵒᵖ)
    (n : (K.X i).val.obj V) :
    (((pullComplex f S T c).obj K).X i).val.obj ((Opens.map f).op.obj V) :=
  ((coefficientAdjunction f S T c).unit.app (K.X i)).val.app V n

variable {S T}

/-- The homogeneous multiplication on an algebra, evaluated on sections.
Source: Stacks, 0FRF (blueprint: lem-sfb-sheaf-dg-pushpull-hom). -/
def mulSection {Y : TopCat.{u}} {R : Y.Sheaf CommRingCat.{u}}
    (A : Algebra R) (p q : ℤ) (U : (Opens Y)ᵒᵖ)
    (a : (A.X.X p).val.obj U) (b : (A.X.X q).val.obj U) :
    (A.X.X (p + q)).val.obj U := actionSection A (regular A) p q U a b

/-- The algebra unit in degree zero.
Source: Stacks, 0FRF (blueprint: lem-sfb-sheaf-dg-pushpull-hom). -/
def oneSection {Y : TopCat.{u}} {R : Y.Sheaf CommRingCat.{u}}
    (A : Algebra R) (U : (Opens Y)ᵒᵖ) : (A.X.X 0).val.obj U :=
  ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
    (𝟙_ (ringedSiteModules.{u} (rings R)))).inv ≫
      (MonObj.one (X := A.X)).f 0).val.app U (1 : R.obj.obj U)

/-- The dg algebra map in its adjoint form C → f_*B. Linearity of map incorporates
compatibility with the coefficient ring map; being a chain map incorporates dφ=φd.
Source: Stacks, 0FRT (blueprint: lem-sfb-sheaf-dg-pushpull-hom). -/
structure AlgebraMap (A : Algebra S) (B : Algebra T) where
  /-- The degreewise coefficient-linear chain map. -/
  map : A.X ⟶ (pushComplex f S T c).obj B.X
  /-- Preservation of multiplication, on homogeneous sections. -/
  mul (p q : ℤ) (V : (Opens Z)ᵒᵖ)
      (a : (A.X.X p).val.obj V) (b : (A.X.X q).val.obj V) :
    (map.f (p + q)).val.app V (mulSection A p q V a b) =
      mulSection B p q ((Opens.map f).op.obj V)
        ((map.f p).val.app V a) ((map.f q).val.app V b)
  /-- Preservation of the unit. -/
  one (V : (Opens Z)ᵒᵖ) :
    (map.f 0).val.app V (oneSection A V) = oneSection B ((Opens.map f).op.obj V)


/-- A pure tensor in the direct-sum total tensor, including its sheafification map.
Source: Stacks, 0FRK (blueprint: lem-sfb-sheaf-dg-pushpull-hom). -/
def totalTensorSection {Y : TopCat.{u}} {R : Y.Sheaf CommRingCat.{u}}
    (K L : Complex R) (p q : ℤ) (U : (Opens Y)ᵒᵖ)
    (x : (K.X p).val.obj U) (y : (L.X q).val.obj U) :
    ((K ⊗ L).X (p + q)).val.obj U :=
  (HomologicalComplex.ιTensorObj K L p q (p + q) rfl).val.app U
    (tensorSection (K.X p) (L.X q) U x y)

variable {f c} {A : Algebra S} {B : Algebra T}

/-- The normalized map used for balancing: (c,n) ↦ (φ(c),1⊗n).
Source: Stacks, 0FR8 (blueprint: lem-sfb-sheaf-dg-pushpull-hom). -/
def IsTensorLift (φ : AlgebraMap f c A B) (N : LeftModule A)
    (t : (pullComplex f S T c).obj (A.X ⊗ N.X) ⟶
      B.X ⊗ (pullComplex f S T c).obj N.X) : Prop :=
  ∀ (p q : ℤ) (V : (Opens Z)ᵒᵖ)
    (a : (A.X.X p).val.obj V) (n : (N.X.X q).val.obj V),
    (t.f (p + q)).val.app ((Opens.map f).op.obj V)
      (pullSection f S T c (A.X ⊗ N.X) (p + q) V
        (totalTensorSection A.X N.X p q V a n)) =
      totalTensorSection B.X ((pullComplex f S T c).obj N.X) p q
        ((Opens.map f).op.obj V) ((φ.map.f p).val.app V a)
          (pullSection f S T c N.X q V n)

/-- The balancing map is uniquely determined by its local tensor formula.
Source: Stacks, 0FR8 and 0FRT (blueprint: lem-sfb-sheaf-dg-pushpull-hom).
Proof: the displayed pairing is coefficient-bilinear after applying the ordinary unit.
The sheaf tensor universal property and coefficient pullback adjunction extend it
uniquely. On each summand the two Leibniz rules and dφ=φd give the chain identity;
coproduct injections detect that identity on the unbounded direct-sum total. -/
theorem existsUnique_tensorLift (φ : AlgebraMap f c A B) (N : LeftModule A) :
    ∃! t : (pullComplex f S T c).obj (A.X ⊗ N.X) ⟶
      B.X ⊗ (pullComplex f S T c).obj N.X, IsTensorLift φ N t := by
  sorry

/-- The canonical balancing map, characterized on original local tensors.
Source: Stacks, 0FR8 (blueprint: lem-sfb-sheaf-dg-pushpull-hom). -/
def tensorLift (φ : AlgebraMap f c A B) (N : LeftModule A) :=
  (existsUnique_tensorLift φ N).choose

/-- The balancing arrow (b,c,n) ↦ (bφ(c),n).
Source: Stacks, 0FRT (blueprint: lem-sfb-sheaf-dg-pushpull-hom). -/
def leftBalance (φ : AlgebraMap f c A B) (N : LeftModule A) :
    (Mod.free B.X).obj ((pullComplex f S T c).obj (A.X ⊗ N.X)) ⟶
      (Mod.free B.X).obj ((pullComplex f S T c).obj N.X) :=
  Mod.freeDesc B.X (tensorLift φ N)

/-- The balancing arrow (b,c,n) ↦ (b,cn).
Source: Stacks, 0FRT (blueprint: lem-sfb-sheaf-dg-pushpull-hom). -/
def rightBalance (_φ : AlgebraMap f c A B) (N : LeftModule A) :
    (Mod.free B.X).obj ((pullComplex f S T c).obj (A.X ⊗ N.X)) ⟶
      (Mod.free B.X).obj ((pullComplex f S T c).obj N.X) :=
  (Mod.free B.X).map ((pullComplex f S T c).map (ModObj.smul (M := A.X) (X := N.X)))

/-- The actual balanced direct-sum total tensor, with its inherited differential.
Its presentation over O_X is B⊗P(N) modulo (bφ(c),n)=(b,cn), where P is ordinary
coefficient pullback. This is also B⊗_{f⁻¹C}f⁻¹N by scalar balancing.
Source: Stacks, 0FRT (blueprint: lem-sfb-sheaf-dg-pushpull-hom). -/
def pullObj (φ : AlgebraMap f c A B) (N : LeftModule A) : LeftModule B :=
  coequalizer (leftBalance φ N) (rightBalance φ N)

/-- The balanced tensor quotient map.
Source: Stacks, 0FRT (blueprint: lem-sfb-sheaf-dg-pushpull-hom). -/
def pullπ (φ : AlgebraMap f c A B) (N : LeftModule A) :
    (Mod.free B.X).obj ((pullComplex f S T c).obj N.X) ⟶ pullObj φ N :=
  coequalizer.π (leftBalance φ N) (rightBalance φ N)

/-- The tensor b⊗x, where x is an arbitrary section of coefficient pullback.
Source: Stacks, 0FR8 (blueprint: lem-sfb-sheaf-dg-pushpull-hom). -/
def pureTensor (φ : AlgebraMap f c A B) (N : LeftModule A)
    (p q : ℤ) (U : (Opens X)ᵒᵖ) (b : (B.X.X p).val.obj U)
    (x : (((pullComplex f S T c).obj N.X).X q).val.obj U) :
    ((pullObj φ N).X.X (p + q)).val.obj U :=
  ((pullπ φ N).hom.f (p + q)).val.app U
    (totalTensorSection B.X ((pullComplex f S T c).obj N.X) p q U b x)

/-- The direct-image action is φ followed by the sectionwise B-action.
Source: Stacks, 0FRT (blueprint: lem-sfb-sheaf-dg-pushpull-hom). -/
def IsPushAction (φ : AlgebraMap f c A B) (M : LeftModule B)
    (a : ModObj A.X ((pushComplex f S T c).obj M.X)) : Prop :=
  ∀ (p q : ℤ) (V : (Opens Z)ᵒᵖ) (x : (A.X.X p).val.obj V)
    (m : (M.X.X q).val.obj ((Opens.map f).op.obj V)),
    actionSection A (moduleOn A _ a) p q V x m =
      actionSection B M p q ((Opens.map f).op.obj V) ((φ.map.f p).val.app V x) m

/-- The prescribed sectionwise action is a unique dg module action.
Source: Stacks, 0FRT (blueprint: lem-sfb-sheaf-dg-pushpull-hom).
Proof: the formula is a natural coefficient-bilinear pairing. Extend it on each
homogeneous tensor summand by sheaf tensor universality. Multiplicativity and
unitality of φ give the module laws, and the Leibniz rule gives the chain identity.
Tensor universality and coproduct injections give uniqueness of the action. -/
theorem existsUnique_pushAction (φ : AlgebraMap f c A B) (M : LeftModule B) :
    ∃! a : ModObj A.X ((pushComplex f S T c).obj M.X), IsPushAction φ M a := by
  sorry

/-- Degreewise direct image with its uniquely prescribed action through φ.
Source: Stacks, 0FRT (blueprint: lem-sfb-sheaf-dg-pushpull-hom). -/
def pushObj (φ : AlgebraMap f c A B) (M : LeftModule B) : LeftModule A :=
  moduleOn A _ (existsUnique_pushAction φ M).choose

/-- Tensoring a chain map gives a unique map on the balanced quotient.
Source: Stacks, 0FRT (blueprint: lem-sfb-sheaf-dg-pushpull-hom).
Proof: action compatibility identifies the two balancing composites. Factor through
the coequalizer; its projection is epi, proving uniqueness. -/
theorem existsUnique_pullMap (φ : AlgebraMap f c A B)
    {N N' : LeftModule A} (g : N ⟶ N') :
    ∃! h : pullObj φ N ⟶ pullObj φ N',
      pullπ φ N ≫ h =
        (Mod.free B.X).map ((pullComplex f S T c).map g.hom) ≫ pullπ φ N' := by
  sorry

/-- Pullback on chain maps is the induced map on balanced tensors.
Source: Stacks, 0FRT (blueprint: lem-sfb-sheaf-dg-pushpull-hom). -/
def pullMap (φ : AlgebraMap f c A B) {N N' : LeftModule A} (g : N ⟶ N') :=
  (existsUnique_pullMap φ g).choose

/-- The balanced tensor maps obey the functor laws.
Source: Stacks, 0FRT (blueprint: lem-sfb-sheaf-dg-pushpull-hom).
Proof: precompose both sides with pullπ. The equations become identity and
composition for coefficient pullback and the free functor. Use uniqueness. -/
theorem pullMap_laws (φ : AlgebraMap f c A B) :
    (∀ N : LeftModule A, pullMap φ (𝟙 N) = 𝟙 (pullObj φ N)) ∧
    (∀ (N N' N'' : LeftModule A) (g : N ⟶ N') (h : N' ⟶ N''),
      pullMap φ (g ≫ h) = pullMap φ g ≫ pullMap φ h) := by
  sorry

/-- Underived dg pullback F, with the balanced direct-sum tensor differential.
Source: Stacks, 0FRT (blueprint: lem-sfb-sheaf-dg-pushpull-hom). -/
def pull (φ : AlgebraMap f c A B) : LeftModule A ⥤ LeftModule B where
  obj := pullObj φ
  map := pullMap φ
  map_id := (pullMap_laws φ).1
  map_comp := (pullMap_laws φ).2 _ _ _

/-- Direct image of a module chain map preserves the prescribed action.
Source: Stacks, 0FRT (blueprint: lem-sfb-sheaf-dg-pushpull-hom).
Proof: evaluate on sections; this is the B-linearity equation for g, with φ(c)
in place of the algebra section. Tensor generators detect the result. -/
theorem pushMap_linear (φ : AlgebraMap f c A B)
    {M M' : LeftModule B} (g : M ⟶ M') :
    IsModHom A.X (@id ((pushObj φ M).X ⟶ (pushObj φ M').X)
      ((pushComplex f S T c).map g.hom)) := by
  sorry

/-- Underived dg direct image G, acting degreewise on the underlying sheaves.
Source: Stacks, 0FRT (blueprint: lem-sfb-sheaf-dg-pushpull-hom). -/
def push (φ : AlgebraMap f c A B) : LeftModule B ⥤ LeftModule A where
  obj := pushObj φ
  map g := { hom := (pushComplex f S T c).map g.hom, isModHom := pushMap_linear φ g }
  map_id M := Mod.hom_ext _ _ ((pushComplex f S T c).map_id M.X)
  map_comp g h := Mod.hom_ext _ _ ((pushComplex f S T c).map_comp g.hom h.hom)


section Hom

variable {Y : TopCat.{u}} {R : Y.Sheaf CommRingCat.{u}}

/-- Signed linearity is closed under the abelian group operations.
Source: Stacks, 0FRL, left convention (blueprint: lem-sfb-sheaf-dg-pushpull-hom).
Proof: distribute each side of the action equation over zero, addition and negation;
composition and tensor whiskering are additive. -/
theorem gradedLinear_group (D : Algebra R) (M N : LeftModule D) (r : ℤ) :
    GradedLinear D M N r 0 ∧
    (∀ h k : CochainComplex.HomComplex.Cochain M.X N.X r,
      GradedLinear D M N r h → GradedLinear D M N r k →
        GradedLinear D M N r (h + k)) ∧
    (∀ h : CochainComplex.HomComplex.Cochain M.X N.X r,
      GradedLinear D M N r h → GradedLinear D M N r (-h)) := by
  sorry

/-- The subgroup of global signed homogeneous module-sheaf maps.
Source: Stacks, 0FRL (blueprint: lem-sfb-sheaf-dg-pushpull-hom). -/
def gradedSubgroup (D : Algebra R) (M N : LeftModule D) (r : ℤ) :
    AddSubgroup (CochainComplex.HomComplex.Cochain M.X N.X r) where
  carrier := GradedLinear D M N r
  zero_mem' := (gradedLinear_group D M N r).1
  add_mem' := (gradedLinear_group D M N r).2.1 _ _
  neg_mem' := (gradedLinear_group D M N r).2.2 _

/-- The Hom differential preserves signed linearity in the resulting degree.
Source: Stacks, 0FRU (blueprint: lem-sfb-sheaf-dg-pushpull-hom).
Proof: if s≠r+1 then δ=0. Otherwise expand d(h(am))-(-1)^r h(d(am)).
The d(a)h(m) terms cancel, leaving (-1)^((r+1)|a|)aδ(h)(m).
This is precisely signed linearity of δh; it uses only the two Leibniz rules. -/
theorem gradedLinear_delta (D : Algebra R) (M N : LeftModule D) (r s : ℤ)
    (h : GradedMap D M N r) :
    GradedLinear D M N s (CochainComplex.HomComplex.δ r s h.val) := by
  sorry

/-- The restriction of δ(h)=d h-(-1)^r h d to signed module maps.
Source: Stacks, 0FRL (blueprint: lem-sfb-sheaf-dg-pushpull-hom). -/
def homDifferential (D : Algebra R) (M N : LeftModule D) (r s : ℤ) :
    AddCommGrpCat.of (gradedSubgroup D M N r) ⟶
      AddCommGrpCat.of (gradedSubgroup D M N s) :=
  AddCommGrpCat.ofHom
    (((CochainComplex.HomComplex.δ_hom ℤ M.X N.X r s).toAddMonoidHom.comp
      (gradedSubgroup D M N r).subtype).codRestrict
        (gradedSubgroup D M N s) (gradedLinear_delta D M N r s))

/-- The restricted differential has cochain shape and square zero.
Source: Stacks, 0FRL (blueprint: lem-sfb-sheaf-dg-pushpull-hom).
Proof: forget the subgroup inclusions. Mathlib's δ_shape and δ_δ prove the
identities on underlying cochains; subgroup inclusions are injective. -/
theorem homDifferential_laws (D : Algebra R) (M N : LeftModule D) :
    (∀ r s : ℤ, ¬ (ComplexShape.up ℤ).Rel r s → homDifferential D M N r s = 0) ∧
    (∀ r s t : ℤ, homDifferential D M N r s ≫ homDifferential D M N s t = 0) := by
  sorry

/-- The global signed module Hom complex, as a complex of actual abelian groups.
Source: Stacks, 0FRL and 0FRU (blueprint: lem-sfb-sheaf-dg-pushpull-hom). -/
def homComplex (D : Algebra R) (M N : LeftModule D) :
    CochainComplex AddCommGrpCat.{u} ℤ where
  X r := AddCommGrpCat.of (gradedSubgroup D M N r)
  d := homDifferential D M N
  shape := (homDifferential_laws D M N).1
  d_comp_d' := fun r s t _ _ ↦ (homDifferential_laws D M N).2 r s t

/-- Composition with a degree-zero module chain map preserves signed linearity.
Source: Stacks, 0FRL (blueprint: lem-sfb-sheaf-dg-pushpull-hom).
Proof: substitute the action equation for the degree-zero map on the appropriate
side of that for h. Its Koszul sign is 1, so h's sign is unchanged. -/
theorem gradedLinear_whisker (D : Algebra R) {L M N P : LeftModule D}
    (a : L ⟶ M) (b : N ⟶ P) (r : ℤ) (h : GradedMap D M N r) :
    GradedLinear D L P r
      (CochainComplex.HomComplex.Cochain.comp
        (CochainComplex.HomComplex.Cochain.comp
          (CochainComplex.HomComplex.Cochain.ofHom a.hom) h.val (zero_add r))
        (CochainComplex.HomComplex.Cochain.ofHom b.hom) (add_zero r)) := by
  sorry

/-- Precomposition and postcomposition of a signed homogeneous map by chain maps.
Source: Stacks, 0FRL (blueprint: lem-sfb-sheaf-dg-pushpull-hom). -/
def whiskerGraded (D : Algebra R) {L M N P : LeftModule D}
    (a : L ⟶ M) (b : N ⟶ P) (r : ℤ) (h : GradedMap D M N r) : GradedMap D L P r :=
  ⟨CochainComplex.HomComplex.Cochain.comp
    (CochainComplex.HomComplex.Cochain.comp
      (CochainComplex.HomComplex.Cochain.ofHom a.hom) h.val (zero_add r))
    (CochainComplex.HomComplex.Cochain.ofHom b.hom) (add_zero r),
      gradedLinear_whisker D a b r h⟩

end Hom

/-- The degreewise ordinary adjoint of a homogeneous map into G(M).
Source: Stacks, 0FR8 (blueprint: lem-sfb-sheaf-dg-pushpull-hom). -/
def adjunctCochain (φ : AlgebraMap f c A B) (N : LeftModule A) (M : LeftModule B)
    (r : ℤ) (k : GradedMap A N (pushObj φ M) r) :
    CochainComplex.HomComplex.Cochain ((pullComplex f S T c).obj N.X) M.X r :=
  CochainComplex.HomComplex.Cochain.mk (fun p q hpq ↦
    ((coefficientAdjunction f S T c).homEquiv (N.X.X p) (M.X.X q)).symm
      (k.val.v p q hpq))

/-- The two explicit formulas for the enriched Hom isomorphism.
The forward map evaluates at 1⊗n and transposes; the inverse uses (-1)^(r p).
HEq transports only integer identities (0+i)+r=i+r and (p+q)+r=p+(q+r).
Source: Stacks, 0FR8 and 0FRU (blueprint: lem-sfb-sheaf-dg-pushpull-hom). -/
def HomFormula (φ : AlgebraMap f c A B)
    (e : ∀ (N : LeftModule A) (M : LeftModule B),
      homComplex B (pullObj φ N) M ≅ homComplex A N (pushObj φ M)) : Prop :=
  (∀ (N : LeftModule A) (M : LeftModule B) (r i : ℤ)
      (h : GradedMap B (pullObj φ N) M r) (V : (Opens Z)ᵒᵖ)
      (n : (N.X.X i).val.obj V),
    HEq ((((e N M).hom.f r h).val.v i (i + r) rfl).val.app V n)
      ((h.val.v (0 + i) (0 + i + r) rfl).val.app ((Opens.map f).op.obj V)
        (pureTensor φ N 0 i ((Opens.map f).op.obj V)
          (oneSection B ((Opens.map f).op.obj V)) (pullSection f S T c N.X i V n)))) ∧
  (∀ (N : LeftModule A) (M : LeftModule B) (r p q : ℤ)
      (k : GradedMap A N (pushObj φ M) r) (U : (Opens X)ᵒᵖ)
      (b : (B.X.X p).val.obj U)
      (x : (((pullComplex f S T c).obj N.X).X q).val.obj U),
    HEq ((((e N M).inv.f r k).val.v (p + q) (p + q + r) rfl).val.app U
        (pureTensor φ N p q U b x))
      (((r * p).negOnePow : ℤ) • actionSection B M p (q + r) U b
        (((adjunctCochain φ N M r k).v q (q + r) rfl).val.app U x)))

/-- Naturality of the enriched isomorphism in both dg module variables.
Source: Stacks, 0FRU (blueprint: lem-sfb-sheaf-dg-pushpull-hom). -/
def HomNaturality (φ : AlgebraMap f c A B)
    (e : ∀ (N : LeftModule A) (M : LeftModule B),
      homComplex B (pullObj φ N) M ≅ homComplex A N (pushObj φ M)) : Prop :=
  ∀ (N N' : LeftModule A) (M M' : LeftModule B) (a : N' ⟶ N) (b : M ⟶ M')
    (r : ℤ) (h : GradedMap B (pullObj φ N) M r),
    (e N' M').hom.f r (whiskerGraded B ((pull φ).map a) b r h) =
      whiskerGraded A a ((push φ).map b) r ((e N M).hom.f r h)

/-- The natural isomorphism of global signed Hom complexes with its specified formulas.
Source: Stacks, sdga.tex, 0FR8 and 0FRU
(blueprint: lem-sfb-sheaf-dg-pushpull-hom).

Proof:
1. Apply the ordinary coefficient-module inverse-image/direct-image adjunction in
   each degree. Finite-input inverse-image uniqueness transports the algebra and
   module structures and detects signed linearity on pairs of original sections.
2. Evaluate h at 1⊗n. Signed linearity gives t(cn)=(-1)^(r|c|)φ(c)t(n).
   Conversely extend t by h(b⊗n)=(-1)^(r|b|)bt(n). The two balancing exponents
   r(p+q) and rp+rq coincide. Sheaf tensor universality extends the maps uniquely
   through the direct-sum tensor and balanced quotient; do not assume global
   sections are pure tensors.
3. Transpose t degreewise to k. The ordinary unit and finite-input inverse-image
   uniqueness identify signed A-linearity on either side. Evaluation and extension
   are additive inverse bijections. Substitution proves naturality in both variables.
4. Expand δh at 1⊗n. Since d(1)=0 the result is dt(n)-(-1)^r t(dn).
   Ordinary adjunction is natural in the differentials, so these additive bijections
   and their inverses commute with δ. They therefore form a chain isomorphism.
5. The displayed forward formula and tensor universality force every component,
   proving uniqueness. No exactness, flatness, or bound enters this construction. -/
theorem existsUnique_homIso (φ : AlgebraMap f c A B) :
    ∃! e : ∀ (N : LeftModule A) (M : LeftModule B),
      homComplex B (pullObj φ N) M ≅ homComplex A N (pushObj φ M),
      HomFormula φ e ∧ HomNaturality φ e := by
  sorry

/-- The canonical enriched adjunction isomorphism, uniquely fixed by evaluation at 1.
Source: Stacks, 0FRU (blueprint: lem-sfb-sheaf-dg-pushpull-hom). -/
def homIso (φ : AlgebraMap f c A B) (N : LeftModule A) (M : LeftModule B) :=
  (existsUnique_homIso φ).choose N M


/-- Unit and counit formulas on sections, including the ordinary evaluation counit.
Source: Stacks, 0FRU and 008K (blueprint: lem-sfb-sheaf-dg-pushpull-hom). -/
def AdjunctionFormula (φ : AlgebraMap f c A B) (a : pull φ ⊣ push φ) : Prop :=
  (∀ (N : LeftModule A) (i : ℤ) (V : (Opens Z)ᵒᵖ) (n : (N.X.X i).val.obj V),
    HEq (((a.unit.app N).hom.f i).val.app V n)
      (pureTensor φ N 0 i ((Opens.map f).op.obj V)
        (oneSection B ((Opens.map f).op.obj V)) (pullSection f S T c N.X i V n))) ∧
  (∀ (M : LeftModule B) (p q : ℤ) (U : (Opens X)ᵒᵖ)
      (b : (B.X.X p).val.obj U)
      (x : (((pullComplex f S T c).obj (pushObj φ M).X).X q).val.obj U),
    ((a.counit.app M).hom.f (p + q)).val.app U (pureTensor φ (pushObj φ M) p q U b x) =
      actionSection B M p q U b
        (((coefficientAdjunction f S T c).counit.app (M.X.X q)).val.app U x))

/-- The degree-zero cycles of the enriched adjunction give the dg module adjunction,
with precisely the stated unit and counit.
Source: Stacks, 0FRU (blueprint: lem-sfb-sheaf-dg-pushpull-hom).
Proof: zero cycles in the signed Hom complex are exactly module chain maps.
Restrict the chain isomorphism to these cycles. Its naturality gives an adjunction.
The identity of F(N) gives the unit 1⊗n; the inverse transpose of id_G(M) gives
b⊗m↦b ev(m). On generators the first triangle sends b⊗n back to b⊗n and the
second sends m to 1⊗m and then m. Ordinary inverse-image triangles and tensor
universality extend these identities. The normalized unit determines the adjunction. -/
theorem existsUnique_adjunction (φ : AlgebraMap f c A B) :
    ∃! a : pull φ ⊣ push φ, AdjunctionFormula φ a := by
  sorry

/-- The dg module adjunction, uniquely determined by its normalized unit and counit.
Source: Stacks, 0FRU (blueprint: lem-sfb-sheaf-dg-pushpull-hom). -/
def adjunction (φ : AlgebraMap f c A B) : pull φ ⊣ push φ :=
  (existsUnique_adjunction φ).choose

/-- Pullback and pushforward respect the signed homotopy relation.
Source: Stacks, 0FRZ (blueprint: lem-sfb-sheaf-dg-pushpull-hom).
Proof: extend a degree -1 homotopy by b⊗n↦(-1)^|b|b⊗h(n). Balancing follows from
signed linearity; the two d(b) terms cancel, leaving the difference of the pulled
chain maps. Direct image carries the same equation sectionwise. Quotient maps
identify the resulting homotopic maps. -/
theorem homotopy_compatible (φ : AlgebraMap f c A B) :
    (∀ (N N' : LeftModule A) (g h : N ⟶ N'), homotopyRel A g h →
      (pull φ ⋙ q B).map g = (pull φ ⋙ q B).map h) ∧
    (∀ (M M' : LeftModule B) (g h : M ⟶ M'), homotopyRel B g h →
      (push φ ⋙ q A).map g = (push φ ⋙ q A).map h) := by
  sorry

/-- The induced pullback on the specified homotopy categories.
Source: Stacks, 0FRZ (blueprint: lem-sfb-sheaf-dg-pushpull-hom). -/
def pullHomotopy (φ : AlgebraMap f c A B) : Homotopy A ⥤ Homotopy B :=
  Quotient.lift (homotopyRel A) (pull φ ⋙ q B) (homotopy_compatible φ).1

/-- The induced pushforward on the specified homotopy categories.
Source: Stacks, 0FRZ (blueprint: lem-sfb-sheaf-dg-pushpull-hom). -/
def pushHomotopy (φ : AlgebraMap f c A B) : Homotopy B ⥤ Homotopy A :=
  Quotient.lift (homotopyRel B) (push φ ⋙ q A) (homotopy_compatible φ).2

/-- The Hom-complex adjunction descends to homotopy classes, with the same unit
and counit after applying the quotient functors.
Source: Stacks, 0FRZ (blueprint: lem-sfb-sheaf-dg-pushpull-hom).
Proof: boundaries in Hom degree zero are precisely differences of homotopic maps.
The chain isomorphism identifies boundaries on both sides; hence its zero-cycle
bijection descends to a natural bijection of homotopy classes. The ordinary unit,
counit and triangle identities descend along the quotient functors. -/
theorem homotopy_adjunction (φ : AlgebraMap f c A B) :
    ∃ a : pullHomotopy φ ⊣ pushHomotopy φ,
      (∀ N : LeftModule A,
        a.unit.app ((q A).obj N) = (q A).map ((adjunction φ).unit.app N)) ∧
      (∀ M : LeftModule B,
        a.counit.app ((q B).obj M) = (q B).map ((adjunction φ).counit.app M)) := by
  sorry

/-- Both dg functors preserve signed shifts and mapping cones, compatibly with
cone inclusions and the specified negative connecting projections.
Source: Stacks, 0FRC, 0FRY and 0FS5 (blueprint: lem-sfb-sheaf-dg-pushpull-hom).
Proof: for every k, the pullback shift comparison is b⊗n↦(-1)^(k|b|)b⊗n;
the pushforward comparison is identity on sections. Shifted action compatibility
uses k(p+q)=kp+kq. The two differential terms have matching exponents k(p+1)
and kp+p+k. The inverses have the same signs. Tensor distributes over the two
finite cone summands; combine this with the k=1 comparison to obtain
b⊗(n',n)↦(b⊗n',(-1)^|b|b⊗n). The off-diagonal differential becomes exactly
F(g)((-1)^|b|b⊗n). Direct image preserves finite sums sectionwise and the cone
matrix entrywise. The inclusion and negative projection diagrams commute. -/
theorem shifts_cones (φ : AlgebraMap f c A B) :
    ∃ (sF : ∀ k : ℤ, shiftFunctor A k ⋙ pull φ ≅ pull φ ⋙ shiftFunctor B k)
      (sG : ∀ k : ℤ, shiftFunctor B k ⋙ push φ ≅ push φ ⋙ shiftFunctor A k),
      (∀ (N N' : LeftModule A) (g : N ⟶ N'),
        ∃ e : pullObj φ (cone A g) ≅ cone B ((pull φ).map g),
          (pull φ).map (coneIn A g) ≫ e.hom = coneIn B ((pull φ).map g) ∧
          e.hom ≫ coneConnecting B ((pull φ).map g) =
            (pull φ).map (coneConnecting A g) ≫ (sF 1).hom.app N) ∧
      (∀ (M M' : LeftModule B) (g : M ⟶ M'),
        ∃ e : pushObj φ (cone B g) ≅ cone A ((push φ).map g),
          (push φ).map (coneIn B g) ≫ e.hom = coneIn A ((push φ).map g) ∧
          e.hom ≫ coneConnecting A ((push φ).map g) =
            (push φ).map (coneConnecting B g) ≫ (sG 1).hom.app M) := by
  sorry

/-- Degreewise transposition commutes with the differentials.
Source: Stacks, 0FRT (blueprint: lem-sfb-sheaf-dg-pushpull-hom).
Proof: transpose both composites by the ordinary coefficient adjunction. Naturality
of its Hom equivalence turns the desired identity into the chain-map equation for φ. -/
theorem baseChangeMap_comm (φ : AlgebraMap f c A B) (i j : ℤ) :
    ((pullComplex f S T c).obj A.X).d i j ≫
        ((coefficientAdjunction f S T c).homEquiv _ _).symm (φ.map.f j) =
      ((coefficientAdjunction f S T c).homEquiv _ _).symm (φ.map.f i) ≫ B.X.d i j := by
  sorry

/-- The coefficient-pullback adjunct P(C) → B of φ, degreewise on complexes.
An isomorphism here means precisely that B is the scalar-base-change algebra
O_X⊗_{f⁻¹O_Z}f⁻¹C with its canonical map (allowing any identified presentation).
Source: Stacks, 0FRT (blueprint: lem-sfb-sheaf-dg-pushpull-hom). -/
def baseChangeMap (φ : AlgebraMap f c A B) : (pullComplex f S T c).obj A.X ⟶ B.X :=
  { f := fun i ↦ ((coefficientAdjunction f S T c).homEquiv _ _).symm (φ.map.f i)
    comm' := fun i j _ ↦ (baseChangeMap_comm φ i j).symm }


/-- Scalar base change contracts the two balanced tensors, naturally, and identifies
both adjunction normalizations with ordinary module-sheaf pullback and pushforward.
The generator equations include the forward map (a⊗c)⊗n↦a⊗cn and its inverse
 a⊗n↦(a⊗1)⊗n; arbitrary a follows by O_X-linearity.
Source: Stacks, 0FRT and 0FRU (blueprint: lem-sfb-sheaf-dg-pushpull-hom).
Proof: use the inverse of baseChangeMap to identify B with P(C). Contract the C
factor against the action of N. The inner coefficient and outer C-balancing make
this well-defined; the inverse inserts 1_C. On generators the composites are
identities because (a⊗1)⊗cn=(a⊗c)⊗n. The two Leibniz rules show differential
compatibility and the construction is natural. Evaluation of the unit and counit
on the same generators gives 1⊗n and a ev(m), respectively. Uniqueness for sheaf
tensors and ordinary pullback gives all section identities. -/
theorem scalarBaseChange (φ : AlgebraMap f c A B) [IsIso (baseChangeMap φ)] :
    ∃ e : pull φ ⋙ Mod.forget B.X ≅ Mod.forget A.X ⋙ pullComplex f S T c,
      (∀ (N : LeftModule A) (p q : ℤ) (V : (Opens Z)ᵒᵖ)
          (a : (A.X.X p).val.obj V) (n : (N.X.X q).val.obj V),
        ((e.hom.app N).f (p + q)).val.app ((Opens.map f).op.obj V)
            (pureTensor φ N p q ((Opens.map f).op.obj V) ((φ.map.f p).val.app V a)
              (pullSection f S T c N.X q V n)) =
          pullSection f S T c N.X (p + q) V (actionSection A N p q V a n)) ∧
      (∀ (N : LeftModule A) (i : ℤ) (V : (Opens Z)ᵒᵖ) (n : (N.X.X i).val.obj V),
        HEq (((e.inv.app N).f i).val.app ((Opens.map f).op.obj V)
            (pullSection f S T c N.X i V n))
          (pureTensor φ N 0 i ((Opens.map f).op.obj V)
            (oneSection B ((Opens.map f).op.obj V)) (pullSection f S T c N.X i V n))) ∧
      (∀ (N : LeftModule A) (i : ℤ),
        ((adjunction φ).unit.app N).hom.f i ≫
            (coefficientPush f S T c).map ((e.hom.app N).f i) =
          (coefficientAdjunction f S T c).unit.app (N.X.X i)) ∧
      (∀ (M : LeftModule B) (i : ℤ),
        (e.hom.app (pushObj φ M)).f i ≫
            (coefficientAdjunction f S T c).counit.app (M.X.X i) =
          ((adjunction φ).counit.app M).hom.f i) := by
  sorry

section Free

variable {Y : TopCat.{u}} {R : Y.Sheaf CommRingCat.{u}}

/-- The identity-space, degree-zero coefficient specialization: the free/forgetful
isomorphism of signed Hom complexes, natural in L and I, with its same formulas.
Source: Stacks, 0FRU and its identity-map specialization
(blueprint: lem-sfb-sheaf-dg-pushpull-hom).
Proof: when f=id and C=O in degree zero, inverse image is identity and the balancing
presentation is the free B-module B⊗L. Evaluate at 1⊗x and extend a degree-r cochain
by b⊗x↦(-1)^(r|b|)bk(x). Balancing is ordinary coefficient linearity. The formulas
are inverse, additive and natural. The differential calculation at 1⊗x is the
same as existsUnique_homIso, so these are inverse chain maps. Their formulas force
uniqueness and identify this adjunction with the general one in this specialization. -/
theorem existsUnique_freeHomIso (D : Algebra R) :
    ∃! e : ∀ (L : Complex R) (I : LeftModule D),
      homComplex D ((Mod.free D.X).obj L) I ≅ CochainComplex.HomComplex L I.X,
      (∀ (L : Complex R) (I : LeftModule D) (r i : ℤ)
          (h : GradedMap D ((Mod.free D.X).obj L) I r) (U : (Opens Y)ᵒᵖ)
          (x : (L.X i).val.obj U),
        HEq (((e L I).hom.f r h).v i (i + r) rfl |>.val.app U <| x)
          ((h.val.v (0 + i) (0 + i + r) rfl).val.app U
            (totalTensorSection D.X L 0 i U (oneSection D U) x))) ∧
      (∀ (L : Complex R) (I : LeftModule D) (r p q : ℤ)
          (k : CochainComplex.HomComplex.Cochain L I.X r) (U : (Opens Y)ᵒᵖ)
          (b : (D.X.X p).val.obj U) (x : (L.X q).val.obj U),
        HEq ((((e L I).inv.f r k).val.v (p + q) (p + q + r) rfl).val.app U
            (totalTensorSection D.X L p q U b x))
          (((r * p).negOnePow : ℤ) • actionSection D I p (q + r) U b
            ((k.v q (q + r) rfl).val.app U x))) ∧
      (∀ (L L' : Complex R) (I I' : LeftModule D) (a : L' ⟶ L) (b : I ⟶ I')
          (r : ℤ) (h : GradedMap D ((Mod.free D.X).obj L) I r),
        (e L' I').hom.f r (whiskerGraded D ((Mod.free D.X).map a) b r h) =
          CochainComplex.HomComplex.Cochain.comp
            (CochainComplex.HomComplex.Cochain.comp
              (CochainComplex.HomComplex.Cochain.ofHom a) ((e L I).hom.f r h)
                (zero_add r))
            (CochainComplex.HomComplex.Cochain.ofHom b.hom) (add_zero r)) := by
  sorry

end Free

end CategoryTheory.SheafDg.Pushpull
