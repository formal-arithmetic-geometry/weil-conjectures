/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O3
-/
module

public import Sheaf.Paper.SixFunctorDatum
public import Sheaf.AlgebraicGeometry.SfOpenExceptionalBaseChange
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Adjunction.Mates
import Sheaf.Paper.ExchangeFunctoriality
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Dual base change

Source: blueprint, sec-six-functors/sk-thm-sf-compatibility,
Dual base change (blueprint: thm-sf-dual-base-change).

The statement is made on the supplied finite-Tor categories.  All maps are the
canonical exchange maps recorded by the datum; no ambient exceptional functor is
introduced.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v w a b c d a₁ b₁ c₁ d₁ e₁ f₁ g₁ h₁ i₁ j₁
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.SuppliedExchangeProjection
namespace WeilConjectures

/-- Restrict a functor to object properties preserved by the supplied datum.
Source: finite-Tor domain convention (blueprint: thm-sf-dual-base-change). -/
def dualBaseChangeRestrict {A : Type a} {B : Type b}
    [Category.{c} A] [Category.{d} B] (P : ObjectProperty A) (Q : ObjectProperty B)
    (F : A ⥤ B) (h : ∀ K : A, P K → Q (F.obj K)) :
    P.FullSubcategory ⥤ Q.FullSubcategory :=
  Q.lift (P.ι ⋙ F) (fun K ↦ h K.obj K.property)

/-- Restrict an adjunction using the same Hom bijections as the original adjunction.
Source: A1 and composite-adjunction construction (blueprint: thm-sf-dual-base-change). -/
def dualBaseChangeRestrictAdjunction {A : Type a} {B : Type b}
    [Category.{c} A] [Category.{d} B] (P : ObjectProperty A) (Q : ObjectProperty B)
    {F : A ⥤ B} {G : B ⥤ A} (adj : F ⊣ G)
    (hF : ∀ K : A, P K → Q (F.obj K)) (hG : ∀ L : B, Q L → P (G.obj L)) :
    dualBaseChangeRestrict P Q F hF ⊣ dualBaseChangeRestrict Q P G hG :=
  adj.restrictFullyFaithful P.fullyFaithfulι Q.fullyFaithfulι (Iso.refl _) (Iso.refl _)

/-- The separated finite-type square domain of the theorem, including its four schemes.
Source: thm-sf-dual-base-change, hypotheses (blueprint: thm-sf-dual-base-change). -/
class DualBaseChangeAdmissible {D : FiniteFieldDatum.{u}}
    (Q : SixFunctorCompactifiedSquare D) : Prop where
  separatedX : IsSeparated Q.X.obj.hom
  separatedY : IsSeparated Q.Y.obj.hom
  separatedX' : IsSeparated Q.X'.obj.hom
  separatedY' : IsSeparated Q.Y'.obj.hom
  separatedF : IsSeparated Q.f.hom.left
  separatedF' : IsSeparated Q.f'.hom.left
  separatedG : IsSeparated Q.g.hom.left
  separatedG' : IsSeparated Q.g'.hom.left
  finiteF : LocallyOfFiniteType Q.f.hom.left
  compactF : QuasiCompact Q.f.hom.left
  finiteF' : LocallyOfFiniteType Q.f'.hom.left
  compactF' : QuasiCompact Q.f'.hom.left
  finiteG : LocallyOfFiniteType Q.g.hom.left
  compactG : QuasiCompact Q.g.hom.left
  finiteG' : LocallyOfFiniteType Q.g'.hom.left
  compactG' : QuasiCompact Q.g'.hom.left

attribute [instance] DualBaseChangeAdmissible.separatedX DualBaseChangeAdmissible.separatedY
  DualBaseChangeAdmissible.separatedX' DualBaseChangeAdmissible.separatedY'
  DualBaseChangeAdmissible.separatedF DualBaseChangeAdmissible.separatedF'
  DualBaseChangeAdmissible.separatedG DualBaseChangeAdmissible.separatedG'
  DualBaseChangeAdmissible.finiteF DualBaseChangeAdmissible.compactF
  DualBaseChangeAdmissible.finiteF' DualBaseChangeAdmissible.compactF'
  DualBaseChangeAdmissible.finiteG DualBaseChangeAdmissible.compactG
  DualBaseChangeAdmissible.finiteG' DualBaseChangeAdmissible.compactG'

/-- A further horizontal base change, sharing the entire middle compactification face.
Source: node proof step 4, horizontal pasting (blueprint: thm-sf-dual-base-change). -/
structure DualBaseChangeHorizontalData {D : FiniteFieldDatum.{u}}
    (Q : SixFunctorCompactifiedSquare D) where
  X : SixFunctorSpace D
  Y : SixFunctorSpace D
  Z : SixFunctorSpace D
  f : X ⟶ Y
  g : Y ⟶ Q.Y'
  g' : X ⟶ Q.X'
  i : X ⟶ Z
  p : Z ⟶ Y
  h : Z ⟶ Q.Z'
  open_i : IsOpenImmersion i.hom.left
  proper_p : IsProper p.hom.left
  factorization : f = i ≫ p
  square : IsPullback g'.hom.left f.hom.left Q.f'.hom.left g.hom.left
  properSquare : IsPullback h.hom.left p.hom.left Q.p'.hom.left g.hom.left
  openSquare : IsPullback g'.hom.left i.hom.left Q.i'.hom.left h.hom.left
  squareComm : g' ≫ Q.f' = f ≫ g
  properComm : h ≫ Q.p' = p ≫ g
  openComm : g' ≫ Q.i' = i ≫ h

/-- The second square of a horizontal paste, with the stipulated shared face.
Source: node proof step 4 (blueprint: thm-sf-dual-base-change). -/
def DualBaseChangeHorizontalData.second {D : FiniteFieldDatum.{u}}
    {Q : SixFunctorCompactifiedSquare D} (R : DualBaseChangeHorizontalData Q) :
    SixFunctorCompactifiedSquare D :=
  { Q with
    X := Q.X'
    Y := Q.Y'
    Z := Q.Z'
    f := Q.f'
    i := Q.i'
    p := Q.p'
    open_i := Q.open_i'
    proper_p := Q.proper_p'
    factorization := Q.factorization'
    X' := R.X
    Y' := R.Y
    Z' := R.Z
    f' := R.f
    g := R.g
    g' := R.g'
    i' := R.i
    p' := R.p
    h := R.h
    open_i' := R.open_i
    proper_p' := R.proper_p
    factorization' := R.factorization
    square := R.square
    properSquare := R.properSquare
    openSquare := R.openSquare
    squareComm := R.squareComm
    properComm := R.properComm
    openComm := R.openComm }

/-- The actual outer horizontal square: all three Cartesian faces are pasted.
Source: node proof step 4 (blueprint: thm-sf-dual-base-change). -/
def DualBaseChangeHorizontalData.pasted {D : FiniteFieldDatum.{u}}
    {Q : SixFunctorCompactifiedSquare D} (R : DualBaseChangeHorizontalData Q) :
    SixFunctorCompactifiedSquare D :=
  { Q with
    X' := R.X
    Y' := R.Y
    Z' := R.Z
    f' := R.f
    g := R.g ≫ Q.g
    g' := R.g' ≫ Q.g'
    i' := R.i
    p' := R.p
    h := R.h ≫ Q.h
    open_i' := R.open_i
    proper_p' := R.proper_p
    factorization' := R.factorization
    square := R.square.paste_horiz Q.square
    properSquare := R.properSquare.paste_horiz Q.properSquare
    openSquare := R.openSquare.paste_horiz Q.openSquare
    squareComm := by
      rw [Category.assoc, Q.squareComm, ← Category.assoc, R.squareComm, Category.assoc]
    properComm := by
      rw [Category.assoc, Q.properComm, ← Category.assoc, R.properComm, Category.assoc]
    openComm := by
      rw [Category.assoc, Q.openComm, ← Category.assoc, R.openComm, Category.assoc] }

/-- Compactification choices for fixed boundaries of a Cartesian square. This is only
an unbundling of SixFunctorCompactifiedSquare, so shared boundaries are definitionally equal.
Source: node proof step 4, arbitrary compactification choices
(blueprint: thm-sf-dual-base-change). -/
structure DualBaseChangeCompactificationData {D : FiniteFieldDatum.{u}}
    {X Y X' Y' : SixFunctorSpace D} (f : X ⟶ Y) (f' : X' ⟶ Y')
    (g : Y' ⟶ Y) (g' : X' ⟶ X) where
  Z : SixFunctorSpace D
  Z' : SixFunctorSpace D
  i : X ⟶ Z
  i' : X' ⟶ Z'
  p : Z ⟶ Y
  p' : Z' ⟶ Y'
  h : Z' ⟶ Z
  open_i : IsOpenImmersion i.hom.left
  open_i' : IsOpenImmersion i'.hom.left
  proper_p : IsProper p.hom.left
  proper_p' : IsProper p'.hom.left
  factorization : f = i ≫ p
  factorization' : f' = i' ≫ p'
  properSquare : IsPullback h.hom.left p'.hom.left p.hom.left g.hom.left
  openSquare : IsPullback g'.hom.left i'.hom.left i.hom.left h.hom.left
  properComm : h ≫ p = p' ≫ g
  openComm : g' ≫ i = i' ≫ h

/-- Rebundle the chosen factors with the given Cartesian boundary.
Source: node proof step 4 (blueprint: thm-sf-dual-base-change). -/
def DualBaseChangeCompactificationData.square {D : FiniteFieldDatum.{u}}
    {X Y X' Y' : SixFunctorSpace D} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} (R : DualBaseChangeCompactificationData f f' g g')
    (sq : IsPullback g'.hom.left f'.hom.left f.hom.left g.hom.left)
    (comm : g' ≫ f = f' ≫ g) : SixFunctorCompactifiedSquare D where
  X := X
  Y := Y
  X' := X'
  Y' := Y'
  f := f
  f' := f'
  g := g
  g' := g'
  Z := R.Z
  Z' := R.Z'
  i := R.i
  i' := R.i'
  p := R.p
  p' := R.p'
  h := R.h
  open_i := R.open_i
  open_i' := R.open_i'
  proper_p := R.proper_p
  proper_p' := R.proper_p'
  factorization := R.factorization
  factorization' := R.factorization'
  square := sq
  squareComm := comm
  properSquare := R.properSquare
  openSquare := R.openSquare
  properComm := R.properComm
  openComm := R.openComm

/-- A vertical Cartesian paste, with arbitrary compactifications of the top and outer
squares. No equality between compactifications of a composite and its factors is assumed.
Source: node proof step 4 (blueprint: thm-sf-dual-base-change). -/
structure DualBaseChangeVerticalData {D : FiniteFieldDatum.{u}}
    (Q : SixFunctorCompactifiedSquare D) where
  W : SixFunctorSpace D
  W' : SixFunctorSpace D
  e : W ⟶ Q.X
  e' : W' ⟶ Q.X'
  g : W' ⟶ W
  square : IsPullback g.hom.left e'.hom.left e.hom.left Q.g'.hom.left
  comm : g ≫ e = e' ≫ Q.g'
  top : DualBaseChangeCompactificationData e e' Q.g' g
  outer : DualBaseChangeCompactificationData (e ≫ Q.f) (e' ≫ Q.f') Q.g g

/-- The upper square of a vertical paste.
Source: node proof step 4 (blueprint: thm-sf-dual-base-change). -/
def DualBaseChangeVerticalData.second {D : FiniteFieldDatum.{u}}
    {Q : SixFunctorCompactifiedSquare D} (R : DualBaseChangeVerticalData Q) :
    SixFunctorCompactifiedSquare D := R.top.square R.square R.comm

/-- The actual outer vertical square, constructed by IsPullback.paste_vert.
Source: node proof step 4 (blueprint: thm-sf-dual-base-change). -/
def DualBaseChangeVerticalData.pasted {D : FiniteFieldDatum.{u}}
    {Q : SixFunctorCompactifiedSquare D} (R : DualBaseChangeVerticalData Q) :
    SixFunctorCompactifiedSquare D :=
  R.outer.square (R.square.paste_vert Q.square)
    (by rw [← Category.assoc, R.comm, Category.assoc, Q.squareComm, ← Category.assoc])

section Stage
variable {D : FiniteFieldDatum.{u}} {B : SixFunctorSpace D → Type v}
    [∀ X, Category.{w} (B X)] (S : SixFunctorPushStage D B)
    {P : ∀ X, ObjectProperty (B X)} (H : SixFunctorCoherentStage S P)

/-- The four operations restricted to the supplied finite-Tor domains.
Source: A1 (blueprint: thm-sf-dual-base-change). -/
def dualCtfPull {X Y : SixFunctorSpace D} (f : X ⟶ Y) [IsSeparated f.hom.left] :=
  dualBaseChangeRestrict (P Y) (P X) (S.pull f) (H.pullDomain f)

/-- Restricted direct image. Source: A1 (blueprint: thm-sf-dual-base-change). -/
def dualCtfDirect {X Y : SixFunctorSpace D} (f : X ⟶ Y) [IsSeparated f.hom.left] :=
  dualBaseChangeRestrict (P X) (P Y) (S.direct f) (H.directDomain f)

/-- Restricted support image. Source: A1 (blueprint: thm-sf-dual-base-change). -/
def dualCtfSupport {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (cf : Compactification f.hom.left) :=
  dualBaseChangeRestrict (P X) (P Y) (S.support f cf) (H.supportDomain f cf)

/-- Restricted exceptional image. Source: A1 (blueprint: thm-sf-dual-base-change). -/
def dualCtfExceptional {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (cf : Compactification f.hom.left) :=
  dualBaseChangeRestrict (P Y) (P X) (S.exceptional f cf) (H.exceptionalDomain f cf)

/-- The restricted A1 adjunctions, with the datum's units and counits.
Source: A1 (blueprint: thm-sf-dual-base-change). -/
def dualCtfPullAdjunction {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] : dualCtfPull S H f ⊣ dualCtfDirect S H f :=
  dualBaseChangeRestrictAdjunction (P Y) (P X) (S.pullDirectAdjunction f)
    (H.pullDomain f) (H.directDomain f)

/-- Restricted exceptional adjunction. Source: A1 (blueprint: thm-sf-dual-base-change). -/
def dualCtfSupportAdjunction {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (cf : Compactification f.hom.left) :
    dualCtfSupport S H f cf ⊣ dualCtfExceptional S H f cf :=
  dualBaseChangeRestrictAdjunction (P X) (P Y) (S.exceptionalAdjunction f cf)
    (H.supportDomain f cf) (H.exceptionalDomain f cf)

section Square
variable (Q : SixFunctorCompactifiedSquare D)
    [IsSeparated Q.f.hom.left] [IsSeparated Q.f'.hom.left]
    [IsSeparated Q.g.hom.left] [IsSeparated Q.g'.hom.left]

/-- The canonical exchange restricted to finite-Tor domains.
Source: A2 (blueprint: thm-sf-dual-base-change). -/
def dualBaseChangeExchange
    (τ : S.support Q.f Q.compactification ⋙ S.pull Q.g ⟶
      S.pull Q.g' ⋙ S.support Q.f' Q.compactification') :
    dualCtfSupport S H Q.f Q.compactification ⋙ dualCtfPull S H Q.g ⟶
      dualCtfPull S H Q.g' ⋙ dualCtfSupport S H Q.f' Q.compactification' :=
  (P Q.Y').fullyFaithfulι.whiskeringRight _ |>.preimage
    (Functor.whiskerLeft (P Q.X).ι τ)

/-- Composite adjunctions for the two sides of the square.
Source: A1 and composite-adjunction construction (blueprint: thm-sf-dual-base-change). -/
def dualBaseChangeLeftAdjunction :=
  (dualCtfSupportAdjunction S H Q.f Q.compactification).comp
    (dualCtfPullAdjunction S H Q.g)

/-- Second pasted adjunction. Source: A1 (blueprint: thm-sf-dual-base-change). -/
def dualBaseChangeRightAdjunction :=
  (dualCtfPullAdjunction S H Q.g').comp
    (dualCtfSupportAdjunction S H Q.f' Q.compactification')

end Square

/-- The conditional square-naturality equation through the actual adjoint comparisons.
Source: fix-lem-exchanges and mate-pasting (blueprint: thm-sf-dual-base-change). -/
structure DualBaseChangeMateLaws
    {A : Type a} {B : Type b} [Category.{c} A] [Category.{d} B]
    {L M : A ⥤ B} {R T : B ⥤ A} (adjL : L ⊣ R) (adjM : M ⊣ T)
    (τ : L ≅ M) (β : R ≅ T) : Prop where
  square : ∀ {A' : Type a} {B' : Type b} [Category.{c} A'] [Category.{d} B']
    {L' M' : A' ⥤ B'} {R' T' : B' ⥤ A'}
    (adjL' : L' ⊣ R') (adjM' : M' ⊣ T') (τ' : L' ≅ M')
    (G : A ⥤ A') (H : B ⥤ B') (x : G ⋙ L' ⟶ L ⋙ H) (y : G ⋙ M' ⟶ M ⋙ H),
    Functor.whiskerLeft G τ'.hom ≫ y = x ≫ Functor.whiskerRight τ.hom H →
    Functor.whiskerRight β.hom G ≫
        (mateEquiv adjM adjM' (TwoSquare.mk _ _ _ _ y)).natTrans =
      (mateEquiv adjL adjL' (TwoSquare.mk _ _ _ _ x)).natTrans ≫
        Functor.whiskerLeft H (conjugateIsoEquiv adjL' adjM' τ'.symm).hom
/-- Proper coincidence on a restricted operation.
Source: A4 (blueprint: thm-sf-dual-base-change). -/
def dualBaseChangeProperIdentification {X Y : SixFunctorSpace D} (g : X ⟶ Y)
    (cg : Compactification g.hom.left) [IsProper g.hom.left] :
    dualCtfSupport S H g cg ≅ dualCtfDirect S H g :=
  (P Y).fullyFaithfulι.whiskeringRight _ |>.preimageIso
    (Functor.isoWhiskerLeft (P X).ι (S.properIdentification g cg))

/-- Restrict the direct composition comparison, whose defining left mate is exactly
S.pullComposition. Source: A1, node step 4 (blueprint: thm-sf-dual-base-change). -/
def dualCtfDirectComposition {X Y Z : SixFunctorSpace D}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f.hom.left] [IsSeparated g.hom.left] [IsSeparated (f ≫ g).hom.left] :
    dualCtfDirect S H (f ≫ g) ≅ dualCtfDirect S H f ⋙ dualCtfDirect S H g :=
  (P Z).fullyFaithfulι.whiskeringRight _ |>.preimageIso
    (Functor.isoWhiskerLeft (P X).ι (sixFunctorDirectComposition S f g))

/-- Restrict the exceptional comparison, the mate of the datum's support composition.
Source: A1 and A4, node step 4 (blueprint: thm-sf-dual-base-change). -/
def dualCtfExceptionalComposition {X Y Z : SixFunctorSpace D}
    (f : X ⟶ Y) (g : Y ⟶ Z) (cf : Compactification f.hom.left)
    (cg : Compactification g.hom.left) (cfg : Compactification (f ≫ g).hom.left) :
    dualCtfExceptional S H (f ≫ g) cfg ≅
      dualCtfExceptional S H g cg ⋙ dualCtfExceptional S H f cf :=
  (P X).fullyFaithfulι.whiskeringRight _ |>.preimageIso
    (Functor.isoWhiskerLeft (P Z).ι (sixFunctorExceptionalComposition S f g cf cg cfg))

/-- A coherent family of the actual compact exchanges on all admissible squares.
Source: A2, node steps 1 and 4 (blueprint: thm-sf-dual-base-change). -/
def DualBaseChangeExchangeFamily :=
  ∀ (Q : SixFunctorCompactifiedSquare D) [DualBaseChangeAdmissible Q],
    dualCtfSupport S H Q.f Q.compactification ⋙ dualCtfPull S H Q.g ≅
      dualCtfPull S H Q.g' ⋙ dualCtfSupport S H Q.f' Q.compactification'

/-- The corresponding family of dual exchanges, retaining their geometric indices.
Source: node steps 2 and 4 (blueprint: thm-sf-dual-base-change). -/
def DualBaseChangeDualFamily :=
  ∀ (Q : SixFunctorCompactifiedSquare D) [DualBaseChangeAdmissible Q],
    dualCtfDirect S H Q.g ⋙ dualCtfExceptional S H Q.f Q.compactification ≅
      dualCtfExceptional S H Q.f' Q.compactification' ⋙ dualCtfDirect S H Q.g'

/-- The horizontal composite of the two actual dual exchanges, conjugated by restricted
direct composition (itself conjugate to pullComposition), with every associator included.
Source: node step 4, beta_gh formula (blueprint: thm-sf-dual-base-change). -/
def dualBaseChangeHorizontalComposite (β : DualBaseChangeDualFamily S H)
    (Q : SixFunctorCompactifiedSquare D) [DualBaseChangeAdmissible Q]
    (R : DualBaseChangeHorizontalData Q) [DualBaseChangeAdmissible R.second]
    [DualBaseChangeAdmissible R.pasted] :
    dualCtfDirect S H R.pasted.g ⋙
        dualCtfExceptional S H R.pasted.f R.pasted.compactification ≅
      dualCtfExceptional S H R.pasted.f' R.pasted.compactification' ⋙
        dualCtfDirect S H R.pasted.g' := by
  letI : IsSeparated R.g.hom.left :=
    DualBaseChangeAdmissible.separatedG (Q := R.second)
  letI : IsSeparated R.g'.hom.left :=
    DualBaseChangeAdmissible.separatedG' (Q := R.second)
  letI : IsSeparated Q.g'.hom.left :=
    DualBaseChangeAdmissible.separatedG' (Q := Q)
  letI : IsSeparated Q.g.hom.left :=
    DualBaseChangeAdmissible.separatedG (Q := Q)
  letI : IsSeparated (R.g ≫ Q.g).hom.left :=
    DualBaseChangeAdmissible.separatedG (Q := R.pasted)
  letI : IsSeparated (R.g' ≫ Q.g').hom.left :=
    DualBaseChangeAdmissible.separatedG' (Q := R.pasted)
  exact Functor.isoWhiskerRight (dualCtfDirectComposition S H R.g Q.g) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (dualCtfDirect S H R.g) (β Q) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (β R.second)
      (@dualCtfDirect D B _ S P H Q.X' Q.X Q.g'
        (DualBaseChangeAdmissible.separatedG' (Q := Q))) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (dualCtfDirectComposition S H R.g' Q.g').symm

/-- The vertical composite of the actual dual exchanges, conjugated by the restricted
exceptional composition comparisons of the datum, with the chosen outer compactification.
Source: node step 4, beta_fe formula (blueprint: thm-sf-dual-base-change). -/
def dualBaseChangeVerticalComposite (β : DualBaseChangeDualFamily S H)
    (Q : SixFunctorCompactifiedSquare D) [DualBaseChangeAdmissible Q]
    (R : DualBaseChangeVerticalData Q) [DualBaseChangeAdmissible R.second]
    [DualBaseChangeAdmissible R.pasted] :
    dualCtfDirect S H R.pasted.g ⋙
        dualCtfExceptional S H R.pasted.f R.pasted.compactification ≅
      dualCtfExceptional S H R.pasted.f' R.pasted.compactification' ⋙
        dualCtfDirect S H R.pasted.g' :=
  Functor.isoWhiskerLeft (dualCtfDirect S H Q.g)
      (dualCtfExceptionalComposition S H R.e Q.f R.second.compactification
        Q.compactification R.pasted.compactification) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (β Q)
      (dualCtfExceptional S H R.e R.second.compactification) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (dualCtfExceptional S H Q.f' Q.compactification') (β R.second) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (dualCtfExceptionalComposition S H R.e' Q.f' R.second.compactification'
        Q.compactification' R.pasted.compactification').symm _

/-- The full stage assertion. The same canonical family beta occurs in the single-square,
horizontal and vertical clauses; pasting is an equation for the constructed outer square.
Source: complete statement of the node (blueprint: thm-sf-dual-base-change). -/
def dualBaseChangeStage
    (ex : ∀ Q : SixFunctorCompactifiedSquare D,
      S.support Q.f Q.compactification ⋙ S.pull Q.g ⟶
        S.pull Q.g' ⋙ S.support Q.f' Q.compactification') : Prop :=
  ∃ (τ : DualBaseChangeExchangeFamily S H) (β : DualBaseChangeDualFamily S H),
    (∀ (Q : SixFunctorCompactifiedSquare D) [DualBaseChangeAdmissible Q],
      (τ Q).hom = dualBaseChangeExchange S H Q (ex Q) ∧
      β Q = conjugateIsoEquiv (dualBaseChangeLeftAdjunction S H Q)
        (dualBaseChangeRightAdjunction S H Q) (τ Q).symm ∧
      (β Q).inv = conjugateEquiv (dualBaseChangeRightAdjunction S H Q)
        (dualBaseChangeLeftAdjunction S H Q) (dualBaseChangeExchange S H Q (ex Q)) ∧
      DualBaseChangeMateLaws (dualBaseChangeLeftAdjunction S H Q)
        (dualBaseChangeRightAdjunction S H Q) (τ Q) (β Q) ∧
      (IsProper Q.g.hom.left → IsProper Q.g'.hom.left) ∧
      (∀ [IsProper Q.g.hom.left] [IsProper Q.g'.hom.left]
        (cg : Compactification Q.g.hom.left) (cg' : Compactification Q.g'.hom.left),
        ∃ βproper : dualCtfSupport S H Q.g cg ⋙
            dualCtfExceptional S H Q.f Q.compactification ≅
          dualCtfExceptional S H Q.f' Q.compactification' ⋙ dualCtfSupport S H Q.g' cg',
        βproper = Functor.isoWhiskerRight
            (dualBaseChangeProperIdentification S H Q.g cg) _ ≪≫ β Q ≪≫
          Functor.isoWhiskerLeft _
            (dualBaseChangeProperIdentification S H Q.g' cg').symm)) ∧
    (∀ (Q : SixFunctorCompactifiedSquare D) [DualBaseChangeAdmissible Q]
      (R : DualBaseChangeHorizontalData Q) [DualBaseChangeAdmissible R.second]
      [DualBaseChangeAdmissible R.pasted],
      β R.pasted = dualBaseChangeHorizontalComposite S H β Q R) ∧
    (∀ (Q : SixFunctorCompactifiedSquare D) [DualBaseChangeAdmissible Q]
      (R : DualBaseChangeVerticalData Q) [DualBaseChangeAdmissible R.second]
      [DualBaseChangeAdmissible R.pasted],
      β R.pasted = dualBaseChangeVerticalComposite S H β Q R)
end Stage

/-- Canonical higher-stage exchange in the datum's named operation coordinates.
Source: A2 and the recorded stage normalizations (blueprint: thm-sf-dual-base-change). -/
def dualBaseChangeHigherExchange {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    {S : SixFunctorPushStage D B} {T : ∀ X, B X ⥤ B X ⥤ B X}
    {Q : SixFunctorCompactifiedSquare D} (A : SixFunctorExchangeData S T Q) :
    S.support Q.f Q.compactification ⋙ S.pull Q.g ⟶
      S.pull Q.g' ⋙ S.support Q.f' Q.compactification' :=
  (eqToIso (congrArg₂ (fun F G ↦ F ⋙ G) A.compactSupport A.horizontal)).inv ≫
    A.stage.compactExchange ≫
    (eqToIso (congrArg₂ (fun F G ↦ F ⋙ G) A.horizontal' A.compactSupport')).hom

/-- Canonical derived pullback comparison, by realization-unit cancellation on complexes.
Source: finite coefficient realization (blueprint: thm-sf-dual-base-change). -/
def dualBaseChangeFinitePullComparison (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (sfIntrinsicDerivedEquivalence Y A).functor ⋙ sfIntrinsicDerivedPullback A f ≅
      (ProEtale.upperStar
        (ModuleCat.{u+1} (ULift.{u+1, u} A)) f).leftDerivedFunctor ⋙
        (sfIntrinsicDerivedEquivalence X A).functor :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      ((sfIntrinsicModuleEquivalence Y A).funInvIdAssoc
        (ProEtale.upperStar (ModuleCat.{u+1} (ULift.{u+1, u} A)) f ⋙
          (sfIntrinsicModuleEquivalence X A).functor)) ≪≫
    Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.isoWhiskerRight
      (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u+1} (ULift.{u+1, u} A)) f).symm _

/-- Remove the intermediate realization using its counit, without choosing any comparison.
Source: finite operation realization (blueprint: thm-sf-dual-base-change). -/
def dualBaseChangeRealization
    {A : Type a} {B : Type b} {A' : Type a₁} {B' : Type b₁}
    {C : Type c₁} {D : Type d₁}
    [Category.{e₁} A] [Category.{f₁} B] [Category.{g₁} A'] [Category.{h₁} B']
    [Category.{i₁} C] [Category.{j₁} D]
    {F : A ⥤ B} {iA : A ⥤ A'} {iB : B ⥤ B'}
    {F' : A' ⥤ B'} {G : C ⥤ D} (eA : C ≌ A') (eB : D ≌ B')
    (α : F ⋙ iB ≅ iA ⋙ F') (γ : eA.functor ⋙ F' ≅ G ⋙ eB.functor) :
    F ⋙ iB ≅ (iA ⋙ eA.inverse) ⋙ G ⋙ eB.functor :=
  α ≪≫ Functor.isoWhiskerLeft iA
    ((eA.invFunIdAssoc F').symm ≪≫ Functor.isoWhiskerLeft eA.inverse γ) ≪≫
    (Functor.associator _ _ _).symm

section Finite
variable (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n)
    (S : SixFunctorOperationDatum D C E n hn) (Q : SixFunctorCompactifiedSquare D)

/-- Source endpoint comparison, with all endpoint functors explicitly fixed.
Source: the finite operation normalizations (blueprint: thm-sf-dual-base-change). -/
def dualBaseChangeFiniteSource :
    (S.finite.support Q.f Q.compactification ⋙ S.finite.pull Q.g) ⋙
        (intrinsicFiniteTorsionConstructible C.l E n hn Q.Y'.obj.left).ι ≅
      ((intrinsicFiniteTorsionConstructible C.l E n hn Q.X.obj.left).ι ⋙
        (sixFunctorFiniteRealization D C E n hn Q.X).inverse) ⋙
      (ProEtale.sfFixedCompactSupport (Padic.coefficientExtensionRing C.l E n)
        Q.compactification ⋙
        (ProEtale.upperStar
          (ModuleCat.{u+1} (ULift.{u+1, u} (Padic.coefficientExtensionRing C.l E n)))
          Q.g.hom.left).leftDerivedFunctor) ⋙
        (sixFunctorFiniteRealization D C E n hn Q.Y').functor :=
  letI := Padic.finite_coefficientExtensionRing C.l E n hn
  dualBaseChangeRealization
    (sixFunctorFiniteRealization D C E n hn Q.X)
    (sixFunctorFiniteRealization D C E n hn Q.Y')
    (sixFunctorCompositeRealization (S.finiteSupport Q.f Q.compactification)
      (S.finitePullback Q.g))
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (ProEtale.sfIntrinsicCompactSupportComparison
          (Padic.coefficientExtensionRing C.l E n) Q.compactification) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        (dualBaseChangeFinitePullComparison (Padic.coefficientExtensionRing C.l E n)
          Q.g.hom.left) ≪≫ (Functor.associator _ _ _).symm)

/-- Target endpoint comparison from the same operation realizations.
Source: the finite operation normalizations (blueprint: thm-sf-dual-base-change). -/
def dualBaseChangeFiniteTarget :
    (S.finite.pull Q.g' ⋙ S.finite.support Q.f' (Q.compactification.ofIsPullback Q.square)) ⋙
        (intrinsicFiniteTorsionConstructible C.l E n hn Q.Y'.obj.left).ι ≅
      ((intrinsicFiniteTorsionConstructible C.l E n hn Q.X.obj.left).ι ⋙
        (sixFunctorFiniteRealization D C E n hn Q.X).inverse) ⋙
      ((ProEtale.upperStar
          (ModuleCat.{u+1} (ULift.{u+1, u} (Padic.coefficientExtensionRing C.l E n)))
          Q.g'.hom.left).leftDerivedFunctor ⋙
        ProEtale.sfFixedCompactSupport (Padic.coefficientExtensionRing C.l E n)
          (Q.compactification.ofIsPullback Q.square)) ⋙
        (sixFunctorFiniteRealization D C E n hn Q.Y').functor :=
  letI := Padic.finite_coefficientExtensionRing C.l E n hn
  dualBaseChangeRealization
    (sixFunctorFiniteRealization D C E n hn Q.X)
    (sixFunctorFiniteRealization D C E n hn Q.Y')
    (sixFunctorCompositeRealization (S.finitePullback Q.g')
      (S.finiteSupport Q.f' (Q.compactification.ofIsPullback Q.square)))
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (dualBaseChangeFinitePullComparison (Padic.coefficientExtensionRing C.l E n)
          Q.g'.hom.left) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        (ProEtale.sfIntrinsicCompactSupportComparison
          (Padic.coefficientExtensionRing C.l E n) (Q.compactification.ofIsPullback Q.square)) ≪≫
      (Functor.associator _ _ _).symm)

/-- The datum's actual finite exchange in operation coordinates, recovered through
its fully faithful inclusion. The actual A2 map `(S.finiteExchangeProjection Q).2.1`
is transported to the supplied base-changed compactification. Both endpoint comparisons
use left-derived pullbacks via `leftDerivedUpperStarIsoMapDerivedCategory`.
The endpoint comparisons are prescribed realization comparisons; no map is freely chosen.
Source: A2 and fix-lem-exchanges (blueprint: thm-sf-dual-base-change). -/
def dualBaseChangeFiniteExchange :
    S.finite.support Q.f Q.compactification ⋙ S.finite.pull Q.g ⟶
      S.finite.pull Q.g' ⋙ S.finite.support Q.f' Q.compactification' :=
  letI := Padic.finite_coefficientExtensionRing C.l E n hn
  ((intrinsicFiniteTorsionConstructible C.l E n hn Q.Y'.obj.left).fullyFaithfulι.whiskeringRight
    _).preimage
    ((dualBaseChangeFiniteSource D C E n hn S Q).hom ≫
      (S.finiteExchangeProjection Q).2.1 ≫
      (dualBaseChangeFiniteTarget D C E n hn S Q).inv) ≫
    Functor.whiskerLeft (S.finite.pull Q.g')
      (S.finite.comparison Q.f' (Q.compactification.ofIsPullback Q.square)
        Q.compactification').hom
end Finite

/-- Dual base change for the finite, integral, rational and common-stage meanings of a
six-functor datum. All operations retain the datum's completed, scalar-localized, or
common-stage coefficient conventions.
Source: blueprint, sec-six-functors/sk-thm-sf-compatibility, node thm-sf-dual-base-change
(blueprint: thm-sf-dual-base-change).

Proof (following the five node steps):

1. Write A = Lg^* Rf_!, B = Rf'_! Lg'^*, R = Rf^! Rg_* and T = Rg'_* Rf'^!.
Restrict the four A1 adjunctions to the supplied domains. Compose their Hom bijections
using def-weil-pbc-composite-adjunction to obtain A ⊣ R and B ⊣ T. A2 gives the specified
exchange τ : A ≅ B. Realization and compactification comparisons express this same map
in the named finite operations; all higher stages use their recorded exchange data.

2. Under def-weil-pbc-adjunction-conjugate, α = τ^c : T ⟶ R has component the unit of
A ⊣ R, followed by RτT, followed by R applied to the counit of B ⊣ T. Conjugating τ⁻¹
gives β : R ⟶ T, with the other unit, Tτ⁻¹R, and the other counit. Conjugation reverses
composition and preserves identities. Hence αβ and βα are identities. This produces a
natural isomorphism, with its forward map the conjugate of the inverse exchange.

3. For a comparison of two squares with endpoint functors G,H and transformations x,y,
fix-lem-exchanges gives (Gτ')y = x(τH). The two conjugate-pasting identities of
lem-weil-pbc-mate-pasting give the corresponding equation for α and the mates of x,y.
Compose with the inverses β on both sides and cancel αβ and βα. The result is precisely
the equation in DualBaseChangeMateLaws.square, including the endpoint functors.

4. Apply the two exchange-pasting equations of fix-lem-exchanges. Conjugation reverses
the composite, and lem-weil-pbc-mate-pasting identifies conjugates of the whiskered
terms with whiskered conjugates under the pasted adjunctions. Taking inverses gives
β_gh = (Rg'_* β_h)(β_g Rh_*) horizontally and
β_fe = (β_e Rf'^!)(Re^! β_f) vertically. Insert the datum's direct composition
comparisons; lem-sf-mate identifies exceptional composition with the conjugate of
support composition. The identity exchange gives identity dual exchange. These are
the two explicit equations for beta on `R.pasted` in `dualBaseChangeStage`; the
composition comparisons are `dualCtfDirectComposition` and `dualCtfExceptionalComposition`.

5. If g is proper, lem-weil-pbc-proper-base-change makes g' proper. A4 supplies
c_g : Rg_! ≅ Rg_* and c_g' : Rg'_! ≅ Rg'_* on the restricted domains. Compose
Rf^! c_g, β, and c_g'⁻¹ Rf'^!. This is the stated βproper, expressed through the same
canonical identifications, so its naturality and pasting follow from those of β.
The argument applies separately to each supplied coefficient stage and never asserts
an exceptional adjunction on an unrestricted ambient category. -/
theorem dualBaseChange
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n)
    (S : SixFunctorDatum D C E n hn) :
    dualBaseChangeStage S.finite S.finiteCoherence
      (dualBaseChangeFiniteExchange D C E n hn S.toSixFunctorOperationDatum) ∧
    dualBaseChangeStage S.higher.integral S.integralCoherence
      (fun Q ↦ dualBaseChangeHigherExchange (S.higher.integralExchange Q)) ∧
    dualBaseChangeStage S.higher.rational S.rationalCoherence
      (fun Q ↦ dualBaseChangeHigherExchange (S.higher.rationalExchange Q)) ∧
    dualBaseChangeStage S.closure.commonStage S.commonCoherence
      (fun Q ↦ dualBaseChangeHigherExchange (S.closure.commonStageExchange Q)) := by
  sorry

end WeilConjectures
