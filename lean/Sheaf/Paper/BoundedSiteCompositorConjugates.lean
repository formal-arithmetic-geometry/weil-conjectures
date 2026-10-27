module

public import Sheaf.Paper.BoundedSiteAdjunctionTranspose
public import Sheaf.Paper.CompactSupportSiteCoherence

/-! # Bounded site comparison of compositor and refinement conjugates

Source: blueprint lem-pur-co-smooth-etale-locality, proof Step 3; Stacks Tags 0B65 and
0DV0 (blueprint: lem-pur-bounded-site-compositor-conjugates).

Finite words retain their actual etale adjunctions. Pro-etale transposition is evaluated
only at bounded etale witnesses, using the published normalized Hom-chain function.
Binary words retain their parenthesization; their evaluators insert the canonical
functor associators, whose components are identities. The pasting syntax below contains
only compactification refinements, compact-support compositors, identities and whiskering.
-/

@[expose] public noncomputable section

set_option autoImplicit false
universe u
open CategoryTheory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.BoundedSiteConjugates

variable (P : WeilConjectures.PurityFiniteSetting.{u})

/-- A chosen compactification and its ordinary etale right adjoint. The dimension bound
is auxiliary finite data, available for every such compactification by
exists_topologicalKrullDim_le, including the empty scheme. No absolute separatedness
is required. Source: node hypotheses and proof Step 1
(blueprint: lem-pur-bounded-site-compositor-conjugates). -/
structure Stage {X Y : Over (Spec (.of P.field.k))} (f : X ⟶ Y) where
  [source_finiteType : LocallyOfFiniteType X.hom]
  [source_quasiCompact : QuasiCompact X.hom]
  [target_finiteType : LocallyOfFiniteType Y.hom]
  [target_quasiCompact : QuasiCompact Y.hom]
  [separated : IsSeparated f.left]
  [finiteType : LocallyOfFiniteType f.left]
  [quasiCompact : QuasiCompact f.left]
  c : Compactification f.left
  dimension : ℕ
  dimension_le : topologicalKrullDim c.Z ≤ (dimension : WithBot ℕ∞)
  right : DerivedCategory (Sheaf Y.left.smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient)) ⥤
    DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))
  adjunction : Etale.rightDerivedLowerShriekOfCompactification
    (ModuleCat.{u + 1} P.Coefficient) c ⊣ right

/-- The morphism indexing a chosen stage.
Source: node hypotheses (blueprint: lem-pur-bounded-site-compositor-conjugates). -/
abbrev Stage.arrow {X Y : Over (Spec (.of P.field.k))} {f : X ⟶ Y}
    (_s : Stage P f) : X ⟶ Y := f

/-- Finite parenthesized words, with empty words for identity adjunctions.
Source: node proof Steps 6--7 (blueprint: lem-pur-bounded-site-compositor-conjugates). -/
inductive Word : Over (Spec (.of P.field.k)) → Over (Spec (.of P.field.k)) → Type (u + 3)
  | single {X Y : Over (Spec (.of P.field.k))} (f : X ⟶ Y) (s : Stage P f) : Word X Y
  | identity (X : Over (Spec (.of P.field.k))) : Word X X
  | comp {X Y Z : Over (Spec (.of P.field.k))} (U : Word X Y) (V : Word Y Z) : Word X Z

variable {P}

/-- The actual bounded-below etale compact-support word.
Source: node proof Step 7 (blueprint: lem-pur-bounded-site-compositor-conjugates). -/
def Word.leftPlus {X Y : Over (Spec (.of P.field.k))} : Word P X Y →
    DerivedCategory.Plus (Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) ⥤
      DerivedCategory.Plus (Sheaf Y.left.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))
  | .single _ s => coherenceEtaleFunctor P.Coefficient s.c
  | .identity _ => 𝟭 _
  | .comp U V => U.leftPlus ⋙ V.leftPlus

/-- The same etale word on the unbounded categories, needed for its ordinary adjunction.
Source: node proof Step 7 (blueprint: lem-pur-bounded-site-compositor-conjugates). -/
def Word.left {X Y : Over (Spec (.of P.field.k))} : Word P X Y →
    DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) ⥤
      DerivedCategory (Sheaf Y.left.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))
  | .single _ s => Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} P.Coefficient) s.c
  | .identity _ => 𝟭 _
  | .comp U V => U.left ⋙ V.left

/-- The actual pro-etale compact-support word.
Source: node proof Step 7 (blueprint: lem-pur-bounded-site-compositor-conjugates). -/
def Word.proLeft {X Y : Over (Spec (.of P.field.k))} : Word P X Y →
    DerivedCategory (Sheaf (Scheme.ProEt.topology X.left) (ModuleCat.{u + 1} P.Coefficient)) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology Y.left) (ModuleCat.{u + 1} P.Coefficient))
  | .single _ s => coherenceProEtaleFunctor P.Coefficient s.c
  | .identity _ => 𝟭 _
  | .comp U V => U.proLeft ⋙ V.proLeft

/-- The reversed word of ordinary etale exceptional inverse images.
Source: node proof Step 7 (blueprint: lem-pur-bounded-site-compositor-conjugates). -/
def Word.right {X Y : Over (Spec (.of P.field.k))} : Word P X Y →
    DerivedCategory (Sheaf Y.left.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) ⥤
      DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))
  | .single _ s => s.right
  | .identity _ => 𝟭 _
  | .comp U V => V.right ⋙ U.right

/-- Each pro-etale exceptional functor is U_Y followed by the etale right adjoint and C_X.
This is the transported functor in def-weil-exceptional-inverse-image, retaining the
specified ordinary adjunction rather than choosing a new one.
Source: node hypotheses (blueprint: lem-pur-bounded-site-compositor-conjugates). -/
def Word.proRight {X Y : Over (Spec (.of P.field.k))} : Word P X Y →
    DerivedCategory (Sheaf (Scheme.ProEt.topology Y.left) (ModuleCat.{u + 1} P.Coefficient)) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology X.left) (ModuleCat.{u + 1} P.Coefficient))
  | .single _ s =>
      (comparisonLowerStar (ModuleCat.{u + 1} P.Coefficient) Y.left).rightDerivedFunctor ⋙
        s.right ⋙ coherenceSiteFunctor P.Coefficient X.left
  | .identity _ => 𝟭 _
  | .comp U V => V.proRight ⋙ U.proRight

/-- The ordinary composite adjunction, with its canonical associators and unitors.
Source: Stacks Tag 0DV0; node proof Steps 4, 6--7
(blueprint: lem-pur-bounded-site-compositor-conjugates). -/
def Word.adjunction {X Y : Over (Spec (.of P.field.k))} (W : Word P X Y) : W.left ⊣ W.right :=
  match W with
  | .single _ s => s.adjunction
  | .identity _ => Adjunction.id
  | .comp U V => U.adjunction.comp V.adjunction

/-- The actual B comparison of a word: B_V followed by F_V(B_U).
Source: node proof Steps 2 and 7 (blueprint: lem-pur-bounded-site-compositor-conjugates). -/
def Word.boundaryIso {X Y : Over (Spec (.of P.field.k))} (W : Word P X Y)
    (J : DerivedCategory.Plus (Sheaf X.left.smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient))) :
    (coherenceSiteFunctor P.Coefficient Y.left).obj (W.leftPlus.obj J).obj ≅
      W.proLeft.obj ((coherenceSiteFunctor P.Coefficient X.left).obj J.obj) :=
  match W with
  | .single _ s => coherenceBoundaryComponent P.Coefficient s.c J
  | .identity _ => Iso.refl _
  | .comp U V => V.boundaryIso (U.leftPlus.obj J) ≪≫ V.proLeft.mapIso (U.boundaryIso J)

/-- Exactly the lower bounds of K and of every intermediate etale exceptional image.
Source: node bounded-domain qualification, proof Step 7
(blueprint: lem-pur-bounded-site-compositor-conjugates). -/
def Word.IntermediateBounds {X Y : Over (Spec (.of P.field.k))} (W : Word P X Y)
    (K : DerivedCategory (Sheaf Y.left.smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient))) : Prop :=
  match W with
  | .comp U V => DerivedCategory.TStructure.t.plus (V.right.obj K) ∧
      U.IntermediateBounds (V.right.obj K) ∧ V.IntermediateBounds K
  | _ => True

/-- The bounded input, output and intermediate images of an exceptional word.
Source: node bounded-domain qualification
(blueprint: lem-pur-bounded-site-compositor-conjugates). -/
def Word.Admissible {X Y : Over (Spec (.of P.field.k))} (W : Word P X Y)
    (K : DerivedCategory (Sheaf Y.left.smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient))) : Prop :=
  DerivedCategory.TStructure.t.plus K ∧ DerivedCategory.TStructure.t.plus (W.right.obj K) ∧
    W.IntermediateBounds K

/-- The comparison a_W, recursively a_U then G_U(a_V), using precisely the comparison unit.
Source: node proof Steps 1, 4 and 7
(blueprint: lem-pur-bounded-site-compositor-conjugates). -/
def Word.rho {X Y : Over (Spec (.of P.field.k))} (W : Word P X Y) :
    ∀ (K : DerivedCategory (Sheaf Y.left.smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient))) (_h : W.Admissible K),
    (coherenceSiteFunctor P.Coefficient X.left).obj (W.right.obj K) ≅
      W.proRight.obj ((coherenceSiteFunctor P.Coefficient Y.left).obj K) :=
  match W with
  | .single _ s => fun K h ↦
      letI := s.source_finiteType
      letI := s.source_quasiCompact
      letI := s.target_finiteType
      letI := s.target_quasiCompact
      letI := s.separated
      letI := s.finiteType
      letI := s.quasiCompact
      haveI := (boundedSiteAdjunctionTranspose P X.hom Y.hom s.arrow.left s.arrow.w s.c
        s.dimension s.dimension_le s.right s.adjunction
        ⟨s.right.obj K, h.2.1⟩ ⟨K, h.1⟩ h.2.1).1
      asIso (boundedSiteRho P.Coefficient s.right K)
  | .identity _ => fun _ _ ↦ Iso.refl _
  | .comp U V => fun K h ↦ U.rho (V.right.obj K) ⟨h.2.2.1, h.2.1, h.2.2.2.1⟩ ≪≫
      U.proRight.mapIso (V.rho K ⟨h.1, h.2.2.1, h.2.2.2.2⟩)

/-- The specified iterated bounded-origin transpose. At a composite, first transpose
through the last word, use B_U to change its source witness, then transpose through U.
This function needs no ambient pro-etale adjunction.
Source: node proof Steps 3--4 and 7
(blueprint: lem-pur-bounded-site-compositor-conjugates). -/
def Word.transpose {X Y : Over (Spec (.of P.field.k))} (W : Word P X Y) :
    ∀ (J : DerivedCategory.Plus (Sheaf X.left.smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient)))
    (L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y.left)
      (ModuleCat.{u + 1} P.Coefficient))),
    (W.proLeft.obj ((coherenceSiteFunctor P.Coefficient X.left).obj J.obj) ⟶ L) →
    ((coherenceSiteFunctor P.Coefficient X.left).obj J.obj ⟶ W.proRight.obj L) :=
  match W with
  | .single _ s => fun J L z ↦ boundedSiteTranspose P.Coefficient s.c s.right s.adjunction J L z
  | .identity _ => fun _ _ z ↦ z
  | .comp U V => fun J L z ↦ U.transpose J (V.proRight.obj L)
      ((U.boundaryIso J).inv ≫ V.transpose (U.leftPlus.obj J) L
        (V.proLeft.map (U.boundaryIso J).hom ≫ z))

/-- The ordinary composite Hom bijection, first through the last word and then the first.
This is Adjunction.comp.homEquiv, with the canonical bounded-below inclusions evaluated.
Source: Stacks Tag 0DV0, node proof Step 4
(blueprint: lem-pur-bounded-site-compositor-conjugates). -/
def Word.homEquiv {X Y : Over (Spec (.of P.field.k))} (W : Word P X Y) :
    ∀ (J : DerivedCategory.Plus (Sheaf X.left.smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient)))
    (K : DerivedCategory (Sheaf Y.left.smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient))),
    ((W.leftPlus.obj J).obj ⟶ K) ≃ (J.obj ⟶ W.right.obj K) :=
  match W with
  | .single _ s => fun J K ↦
      ((Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
        (ModuleCat.{u + 1} P.Coefficient) s.c).app J).homFromEquiv.trans
          (s.adjunction.homEquiv J.obj K)
  | .identity _ => fun _ _ ↦ Equiv.refl _
  | .comp U V => fun J K ↦ (V.homEquiv (U.leftPlus.obj J) K).trans
      (U.homEquiv J (V.right.obj K))

/-- The actual ordinary composite counit, as the inverse transpose of the identity.
Source: Stacks Tags 0B65, 0DV0; node proof Steps 2, 4 and 8
(blueprint: lem-pur-bounded-site-compositor-conjugates). -/
def Word.counit {X Y : Over (Spec (.of P.field.k))} (W : Word P X Y)
    (K : DerivedCategory (Sheaf Y.left.smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient))) (h : W.Admissible K) :
    (W.leftPlus.obj ⟨W.right.obj K, h.2.1⟩).obj ⟶ K :=
  (W.homEquiv ⟨W.right.obj K, h.2.1⟩ K).symm (𝟙 _)

/-- Finite compatible left-adjoint pastings. Refinement and composition constructors use
exactly the recorded chosen arrows. Whiskering changes etale-origin witnesses via B;
associators and unitors have their canonical identity components.
Source: node proof Steps 5--8
(blueprint: lem-pur-bounded-site-compositor-conjugates). -/
inductive Paste : {X Y : Over (Spec (.of P.field.k))} → Word P X Y → Word P X Y →
    Type (u + 3)
  | identity {X Y : Over (Spec (.of P.field.k))} (W : Word P X Y) : Paste W W
  | refinement {X Y : Over (Spec (.of P.field.k))} {f : X ⟶ Y}
      (s t : Stage P f) (r : s.c.Refinement t.c) :
      Paste (.single f s) (.single f t)
  | compositor {X Y Z : Over (Spec (.of P.field.k))} {f : X ⟶ Y} {g : Y ⟶ Z}
      (s : Stage P f) (t : Stage P g) (v : Stage P (f ≫ g)) :
      Paste (.comp (.single f s) (.single g t)) (.single (f ≫ g) v)
  | vertical {X Y : Over (Spec (.of P.field.k))} {U V W : Word P X Y}
      (D : Paste U V) (E : Paste V W) : Paste U W
  | before {X Y Z : Over (Spec (.of P.field.k))} (W : Word P X Y)
      {U V : Word P Y Z} (D : Paste U V) : Paste (.comp W U) (.comp W V)
  | after {X Y Z : Over (Spec (.of P.field.k))} {U V : Word P X Y}
      (D : Paste U V) (W : Word P Y Z) : Paste (.comp U W) (.comp V W)
  | associator {X Y Z T : Over (Spec (.of P.field.k))}
      (U : Word P X Y) (V : Word P Y Z) (W : Word P Z T) :
      Paste (.comp (.comp U V) W) (.comp U (.comp V W))
  | leftUnitor {X Y : Over (Spec (.of P.field.k))} (W : Word P X Y) :
      Paste (.comp (.identity X) W) W
  | rightUnitor {X Y : Over (Spec (.of P.field.k))} (W : Word P X Y) :
      Paste (.comp W (.identity Y)) W

/-- Evaluate the specified left-adjoint diagram on the etale site.
Source: node proof Steps 2, 5--8
(blueprint: lem-pur-bounded-site-compositor-conjugates). -/
def Paste.etaleMap {X Y : Over (Spec (.of P.field.k))} {U V : Word P X Y}
    (D : Paste U V) :
    ∀ (J : DerivedCategory.Plus (Sheaf X.left.smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient))), U.leftPlus.obj J ⟶ V.leftPlus.obj J :=
  match D with
  | .identity _ => fun _ ↦ 𝟙 _
  | .refinement s t r => fun J ↦
      letI := s.quasiCompact
      (Etale.rightDerivedLowerShriekOfCompactificationPlusRefinementIso
        P.Coefficient r).inv.app J
  | .compositor s t v => fun J ↦
      letI := s.quasiCompact
      letI := t.quasiCompact
      (coherenceEtaleCompositor P.Coefficient s.c t.c v.c).hom.app J
  | .vertical D E => fun J ↦ D.etaleMap J ≫ E.etaleMap J
  | .before W D => fun J ↦ D.etaleMap (W.leftPlus.obj J)
  | .after D W => fun J ↦ W.leftPlus.map (D.etaleMap J)
  | .associator _ _ _ => fun _ ↦ 𝟙 _
  | .leftUnitor _ => fun _ ↦ 𝟙 _
  | .rightUnitor _ => fun _ ↦ 𝟙 _

/-- Evaluate the actual pro-etale left arrows, transporting sources by their specified B
witnesses when whiskering before a diagram. No etale arrow is used to define these maps.
Source: node proof Steps 2, 5 and 8
(blueprint: lem-pur-bounded-site-compositor-conjugates). -/
def Paste.proMap {X Y : Over (Spec (.of P.field.k))} {U V : Word P X Y}
    (D : Paste U V) :
    ∀ (J : DerivedCategory.Plus (Sheaf X.left.smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient))),
    U.proLeft.obj ((coherenceSiteFunctor P.Coefficient X.left).obj J.obj) ⟶
      V.proLeft.obj ((coherenceSiteFunctor P.Coefficient X.left).obj J.obj) :=
  match D with
  | .identity _ => fun _ ↦ 𝟙 _
  | .refinement s t r => fun J ↦ (properTransportRefinement P.Coefficient r J).hom
  | .compositor s t v => fun J ↦
      letI := s.quasiCompact
      letI := t.quasiCompact
      coherenceProEtaleCompositor P.Coefficient s.c t.c v.c J
  | .vertical D E => fun J ↦ D.proMap J ≫ E.proMap J
  | @Paste.before _ _ _ _ W U V D => fun J ↦
      U.proLeft.map (W.boundaryIso J).inv ≫ D.proMap (W.leftPlus.obj J) ≫
        V.proLeft.map (W.boundaryIso J).hom
  | .after D W => fun J ↦ W.proLeft.map (D.proMap J)
  | .associator _ _ _ => fun _ ↦ 𝟙 _
  | .leftUnitor _ => fun _ ↦ 𝟙 _
  | .rightUnitor _ => fun _ ↦ 𝟙 _

/-- The bounded intermediate exceptional objects encountered inside a pasted diagram.
Source: node bounded-domain qualification and proof Steps 7--8
(blueprint: lem-pur-bounded-site-compositor-conjugates). -/
def Paste.IntermediateBounds {X Y : Over (Spec (.of P.field.k))} {U V : Word P X Y}
    (D : Paste U V)
    (K : DerivedCategory (Sheaf Y.left.smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient))) : Prop :=
  match D with
  | @Paste.vertical _ _ _ _ W _ D E => W.Admissible K ∧
      D.IntermediateBounds K ∧ E.IntermediateBounds K
  | .before _ D => D.IntermediateBounds K
  | .after D W => D.IntermediateBounds (W.right.obj K)
  | _ => True

/-- The etale conjugate is the transpose of the chosen left arrow followed by its counit.
Source: Stacks Tag 0B65; node displayed definition of t, proof Steps 4--5
(blueprint: lem-pur-bounded-site-compositor-conjugates). -/
def Paste.etaleConjugate {X Y : Over (Spec (.of P.field.k))} {U V : Word P X Y}
    (D : Paste U V)
    (K : DerivedCategory (Sheaf Y.left.smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient))) (hV : V.Admissible K) :
    V.right.obj K ⟶ U.right.obj K :=
  U.homEquiv ⟨V.right.obj K, hV.2.1⟩ K
    ((D.etaleMap ⟨V.right.obj K, hV.2.1⟩).hom ≫ V.counit K hV)

/-- The actual bounded-origin pro-etale conjugate, evaluated using the witness a_V.
The arrow B_V inverse followed by C(epsilon_V) is F_V(a_V) followed by the normalized
pro-etale counit, by boundedSiteAdjunctionTranspose iterated along V. Thus this is the
specified transpose of epsilon_V alpha, with only the canonical source witness inserted.
It is not defined by taking the C-image of the etale conjugate.
Source: Stacks Tag 0B65; node proof Steps 1--5, 7--8
(blueprint: lem-pur-bounded-site-compositor-conjugates). -/
def Paste.proConjugate {X Y : Over (Spec (.of P.field.k))} {U V : Word P X Y}
    (D : Paste U V)
    (K : DerivedCategory (Sheaf Y.left.smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient))) (hV : V.Admissible K) :
    V.proRight.obj ((coherenceSiteFunctor P.Coefficient Y.left).obj K) ⟶
      U.proRight.obj ((coherenceSiteFunctor P.Coefficient Y.left).obj K) :=
  (V.rho K hV).inv ≫ U.transpose ⟨V.right.obj K, hV.2.1⟩
    ((coherenceSiteFunctor P.Coefficient Y.left).obj K)
    (D.proMap ⟨V.right.obj K, hV.2.1⟩ ≫
      (V.boundaryIso ⟨V.right.obj K, hV.2.1⟩).inv ≫
      (coherenceSiteFunctor P.Coefficient Y.left).map (V.counit K hV))

/-- The pasted right-adjoint diagram: vertical arrows reverse, before-whiskering applies
the right functor, and after-whiskering evaluates at its canonical etale-origin witness.
Only the primitive refinement and compositor arrows are transposed. Thus comparison with
the conjugate of the entire left paste is a genuine pasting assertion.
Source: node proof Step 8; Stacks Tags 0B65 and 0DV0
(blueprint: lem-pur-bounded-site-compositor-conjugates). -/
def Paste.rightMap {X Y : Over (Spec (.of P.field.k))} {U V : Word P X Y}
    (D : Paste U V) :
    ∀ (K : DerivedCategory (Sheaf Y.left.smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient)))
    (_hU : U.Admissible K) (_hV : V.Admissible K) (_hD : D.IntermediateBounds K),
    V.proRight.obj ((coherenceSiteFunctor P.Coefficient Y.left).obj K) ⟶
      U.proRight.obj ((coherenceSiteFunctor P.Coefficient Y.left).obj K) :=
  match D with
  | .identity _ => fun _ _ _ _ ↦ 𝟙 _
  | .refinement s t r => fun K _ hV _ ↦ (Paste.refinement s t r).proConjugate K hV
  | .compositor s t v => fun K _ hV _ ↦ (Paste.compositor s t v).proConjugate K hV
  | .vertical D E => fun K hU hV hD ↦
      E.rightMap K hD.1 hV hD.2.2 ≫ D.rightMap K hU hD.1 hD.2.1
  | .before W D => fun K hU hV hD ↦ W.proRight.map
      (D.rightMap K ⟨hU.1, hU.2.2.1, hU.2.2.2.2⟩
        ⟨hV.1, hV.2.2.1, hV.2.2.2.2⟩ hD)
  | @Paste.after _ _ _ _ U V D W => fun K hU hV hD ↦
      V.proRight.map (W.rho K ⟨hU.1, hU.2.2.1, hU.2.2.2.2⟩).inv ≫
        D.rightMap (W.right.obj K) ⟨hU.2.2.1, hU.2.1, hU.2.2.2.1⟩
          ⟨hV.2.2.1, hV.2.1, hV.2.2.2.1⟩ hD ≫
        U.proRight.map (W.rho K ⟨hU.1, hU.2.2.1, hU.2.2.2.2⟩).hom
  | .associator _ _ _ => fun _ _ _ _ ↦ 𝟙 _
  | .leftUnitor _ => fun _ _ _ _ ↦ 𝟙 _
  | .rightUnitor _ => fun _ _ _ _ ↦ 𝟙 _

private theorem hom_left {X Y : Over (Spec (.of P.field.k))} (W : Word P X Y)
    {J J' : DerivedCategory.Plus (Sheaf X.left.smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient))}
    (K : DerivedCategory (Sheaf Y.left.smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient))) (b : J' ⟶ J)
    (z : (W.leftPlus.obj J).obj ⟶ K) :
    W.homEquiv J' K ((W.leftPlus.map b).hom ≫ z) =
      b.hom ≫ W.homEquiv J K z := by
  induction W with
  | single f s =>
      dsimp [Word.homEquiv, Word.leftPlus, Iso.homFromEquiv]
      erw [← Category.assoc,
        ← (Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
          (ModuleCat.{u + 1} P.Coefficient) s.c).inv.naturality b]
      rw [Category.assoc]
      exact s.adjunction.homEquiv_naturality_left b.hom _
  | identity => rfl
  | comp U V ihU ihV =>
      dsimp [Word.homEquiv, Word.leftPlus, Iso.homFromEquiv]
      erw [ihV, ihU]
      rfl

private theorem hom_right {X Y : Over (Spec (.of P.field.k))} (W : Word P X Y)
    (J : DerivedCategory.Plus (Sheaf X.left.smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient)))
    {K K' : DerivedCategory (Sheaf Y.left.smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient))}
    (z : (W.leftPlus.obj J).obj ⟶ K) (b : K ⟶ K') :
    W.homEquiv J K' (z ≫ b) = W.homEquiv J K z ≫ W.right.map b := by
  induction W with
  | single f s =>
      dsimp [Word.homEquiv, Word.right, Iso.homFromEquiv]
      rw [← Category.assoc]
      exact s.adjunction.homEquiv_naturality_right _ b
  | identity => rfl
  | comp U V ihU ihV =>
      dsimp [Word.homEquiv, Word.right, Iso.homFromEquiv]
      erw [ihV, ihU]
      rfl

private theorem boundary_naturality {X Y : Over (Spec (.of P.field.k))} (W : Word P X Y)
    {J J' : DerivedCategory.Plus (Sheaf X.left.smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient))} (b : J ⟶ J') :
    (coherenceSiteFunctor P.Coefficient Y.left).map (W.leftPlus.map b).hom ≫
        (W.boundaryIso J').hom =
      (W.boundaryIso J).hom ≫ W.proLeft.map
        ((coherenceSiteFunctor P.Coefficient X.left).map b.hom) := by
  induction W with
  | single f s => exact (coherenceBoundaryIso P.Coefficient s.c).hom.naturality b
  | identity => simp [Word.leftPlus, Word.proLeft, Word.boundaryIso]
  | comp U V ihU ihV =>
      dsimp [Word.leftPlus, Word.proLeft, Word.boundaryIso]
      rw [← Category.assoc, ihV, Category.assoc, ← V.proLeft.map_comp, ihU,
        V.proLeft.map_comp, Category.assoc]

private theorem transpose_right {X Y : Over (Spec (.of P.field.k))} (W : Word P X Y)
    (J : DerivedCategory.Plus (Sheaf X.left.smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient)))
    {L L' : DerivedCategory (Sheaf (Scheme.ProEt.topology Y.left)
      (ModuleCat.{u + 1} P.Coefficient))}
    (z : W.proLeft.obj ((coherenceSiteFunctor P.Coefficient X.left).obj J.obj) ⟶ L)
    (b : L ⟶ L') :
    W.transpose J L' (z ≫ b) = W.transpose J L z ≫ W.proRight.map b := by
  induction W with
  | single f s =>
      dsimp [Word.transpose, boundedSiteTranspose, Word.proRight]
      rw [← Category.assoc, Adjunction.homEquiv_naturality_right,
        Adjunction.homEquiv_naturality_right]
      erw [Adjunction.homEquiv_naturality_right, Functor.map_comp]
      rfl
  | identity => rfl
  | comp U V ihU ihV =>
      dsimp [Word.transpose, Word.proRight]
      rw [← Category.assoc, ihV, ← Category.assoc, ihU]

private theorem transpose_compatible {X Y : Over (Spec (.of P.field.k))}
    (W : Word P X Y)
    (J : DerivedCategory.Plus (Sheaf X.left.smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient)))
    (K : DerivedCategory (Sheaf Y.left.smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient))) (h : W.Admissible K)
    (z : (W.leftPlus.obj J).obj ⟶ K) :
    W.transpose J ((coherenceSiteFunctor P.Coefficient Y.left).obj K)
        ((W.boundaryIso J).inv ≫ (coherenceSiteFunctor P.Coefficient Y.left).map z) =
      (coherenceSiteFunctor P.Coefficient X.left).map (W.homEquiv J K z) ≫
        (W.rho K h).hom := by
  induction W with
  | single f s =>
      change boundedSiteTranspose P.Coefficient s.c s.right s.adjunction J
          ((coherenceSiteFunctor P.Coefficient _).obj K)
          ((coherenceBoundaryComponent P.Coefficient s.c J).inv ≫
            (coherenceSiteFunctor P.Coefficient _).map z) =
        (coherenceSiteFunctor P.Coefficient _).map
          (s.adjunction.homEquiv J.obj K
            (((Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
              (ModuleCat.{u + 1} P.Coefficient) s.c).app J).inv ≫ z)) ≫
          boundedSiteRho P.Coefficient s.right K
      have hb : (compactSupportSiteComparison P.Coefficient s.c).inv.app J ≫
          (coherenceBoundaryComponent P.Coefficient s.c J).inv =
        (coherenceSiteFunctor P.Coefficient _).map
          ((Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
            (ModuleCat.{u + 1} P.Coefficient) s.c).inv.app J) := by
        simp only [coherenceBoundaryComponent, coherenceEvaluateSquare, coherenceBoundaryIso,
          compactExchangeTransportComparison, Iso.trans_inv, Iso.symm_inv, Iso.app_inv,
          NatTrans.comp_app, Functor.isoWhiskerRight_inv, Functor.whiskerRight_app,
          Functor.associator_hom_app, Functor.associator_inv_app, Category.comp_id]
        rw [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
        rfl
      unfold boundedSiteTranspose
      rw [← Category.assoc, hb, ← Functor.map_comp]
      have he : (derivedComparisonAdjunction (ModuleCat.{u + 1} P.Coefficient) _).homEquiv
          _ _ ((coherenceSiteFunctor P.Coefficient _).map
            (((Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
              (ModuleCat.{u + 1} P.Coefficient) s.c).inv.app J) ≫ z)) =
          (((Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
            (ModuleCat.{u + 1} P.Coefficient) s.c).inv.app J) ≫ z) ≫
            (derivedComparisonAdjunction (ModuleCat.{u + 1} P.Coefficient) _).unit.app K := by
        rw [Adjunction.homEquiv_unit]
        exact (((derivedComparisonAdjunction
          (ModuleCat.{u + 1} P.Coefficient) _).unit).naturality _).symm
      erw [he, s.adjunction.homEquiv_naturality_right, Functor.map_comp]
      rfl
  | identity =>
      change 𝟙 _ ≫ (coherenceSiteFunctor P.Coefficient _).map z =
        (coherenceSiteFunctor P.Coefficient _).map z ≫ 𝟙 _
      simp only [Category.id_comp, Category.comp_id]
  | comp U V ihU ihV =>
      simp only [Word.transpose, Word.boundaryIso, Word.rho, Word.homEquiv,
        Word.leftPlus, Word.proLeft, Word.proRight, Functor.comp_obj,
        Iso.trans_inv, Iso.trans_hom, Functor.mapIso_inv, Functor.mapIso_hom,
        Equiv.trans_apply, ← Category.assoc, ← Functor.map_comp,
        Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]
      rw [ihV (U.leftPlus.obj J) K ⟨h.1, h.2.2.1, h.2.2.2.2⟩ z, ← Category.assoc, transpose_right,
        ihU J (V.right.obj K) ⟨h.2.2.1, h.2.1, h.2.2.2.1⟩]
      simp only [Category.assoc]
      rfl

private theorem paste_square {X Y : Over (Spec (.of P.field.k))} {U V : Word P X Y}
    (D : Paste U V)
    (J : DerivedCategory.Plus (Sheaf X.left.smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient))) :
    (coherenceSiteFunctor P.Coefficient Y.left).map (D.etaleMap J).hom ≫
        (V.boundaryIso J).hom = (U.boundaryIso J).hom ≫ D.proMap J := by
  induction D with
  | identity W =>
      dsimp only [Paste.etaleMap, Paste.proMap]
      simp only [ObjectProperty.FullSubcategory.id_hom, CategoryTheory.Functor.map_id,
        Category.id_comp, Category.comp_id]
  | refinement s t r =>
      let := s.source_finiteType
      let := s.source_quasiCompact
      let := s.target_finiteType
      let := s.target_quasiCompact
      let := s.separated
      let := s.finiteType
      let := s.quasiCompact
      exact (compactSupportSiteCoherence P).2.2.1
        (CompactSupportSiteDiagram.refinement r J)
  | compositor s t v =>
      let := s.source_finiteType
      let := s.source_quasiCompact
      let := s.target_finiteType
      let := s.target_quasiCompact
      let := t.target_finiteType
      let := t.target_quasiCompact
      let := s.separated
      let := s.finiteType
      let := s.quasiCompact
      let := t.separated
      let := t.finiteType
      let := t.quasiCompact
      exact (compactSupportSiteCoherence P).2.2.1
        (CompactSupportSiteDiagram.composition s.c t.c v.c J)
  | vertical D E ihD ihE =>
      dsimp [Paste.etaleMap, Paste.proMap]
      rw [Functor.map_comp, Category.assoc, ihE, ← Category.assoc, ihD, Category.assoc]
  | before W D ih =>
      dsimp [Paste.etaleMap, Paste.proMap, Word.boundaryIso]
      rw [← Category.assoc, ih, Category.assoc]
      simp only [← Functor.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
        Category.id_comp, Category.assoc]
  | after D W ih =>
      dsimp [Paste.etaleMap, Paste.proMap, Word.boundaryIso]
      rw [← Category.assoc, boundary_naturality W, Category.assoc,
        ← W.proLeft.map_comp, ih, W.proLeft.map_comp, Category.assoc]
  | associator U V W =>
      dsimp only [Paste.etaleMap, Paste.proMap, Word.boundaryIso, Word.leftPlus, Word.proLeft]
      simp only [ObjectProperty.FullSubcategory.id_hom, Iso.trans_hom, Functor.mapIso_hom,
        Functor.comp_obj, Functor.comp_map, CategoryTheory.Functor.map_id, Category.id_comp,
        Category.comp_id, Functor.map_comp, Category.assoc]
  | leftUnitor W =>
      dsimp only [Paste.etaleMap, Paste.proMap, Word.boundaryIso, Word.leftPlus, Word.proLeft]
      simp only [ObjectProperty.FullSubcategory.id_hom, Iso.trans_hom, Functor.mapIso_hom,
        Iso.refl_hom, Functor.comp_obj, Functor.id_obj, CategoryTheory.Functor.map_id,
        Category.id_comp, Category.comp_id]
  | rightUnitor W =>
      dsimp only [Paste.etaleMap, Paste.proMap, Word.boundaryIso, Word.leftPlus, Word.proLeft]
      simp only [ObjectProperty.FullSubcategory.id_hom, Iso.trans_hom, Functor.mapIso_hom,
        Iso.refl_hom, Functor.comp_obj, Functor.id_obj, Functor.id_map,
        CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

private theorem conjugate_comparison
    {X Y : Over (Spec (.of P.field.k))} {U V : Word P X Y} (D : Paste U V)
    (K : DerivedCategory (Sheaf Y.left.smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient))) (hU : U.Admissible K) (hV : V.Admissible K) :
    (coherenceSiteFunctor P.Coefficient X.left).map (D.etaleConjugate K hV) ≫
        (U.rho K hU).hom = (V.rho K hV).hom ≫ D.proConjugate K hV := by
  unfold Paste.proConjugate Paste.etaleConjugate
  simp only [Iso.hom_inv_id_assoc]
  rw [← transpose_compatible U _ K hU]
  congr 1
  have hs := paste_square D ⟨V.right.obj K, hV.2.1⟩
  apply (cancel_epi (U.boundaryIso ⟨V.right.obj K, hV.2.1⟩).hom).mp
  simp only [Iso.hom_inv_id_assoc, Functor.map_comp]
  rw [← reassoc_of% hs]
  simp only [Iso.hom_inv_id_assoc]

private theorem rho_naturality {X Y : Over (Spec (.of P.field.k))} (W : Word P X Y)
    {K K' : DerivedCategory (Sheaf Y.left.smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient))}
    (h : W.Admissible K) (h' : W.Admissible K') (b : K ⟶ K') :
    (coherenceSiteFunctor P.Coefficient X.left).map (W.right.map b) ≫
        (W.rho K' h').hom =
      (W.rho K h).hom ≫ W.proRight.map
        ((coherenceSiteFunctor P.Coefficient Y.left).map b) := by
  induction W with
  | single f s =>
      dsimp only [Word.right, Word.proRight, Functor.comp_map]
      change _ ≫ boundedSiteRho P.Coefficient s.right K' =
        boundedSiteRho P.Coefficient s.right K ≫ _
      simp only [boundedSiteRho, coherenceSiteFunctor, ← Functor.map_comp]
      exact congrArg (fun z ↦ (coherenceSiteFunctor P.Coefficient _).map (s.right.map z))
        ((derivedComparisonAdjunction (ModuleCat.{u + 1} P.Coefficient) _).unit.naturality b)
  | identity => simp [Word.right, Word.rho, Word.proRight]
  | comp U V ihU ihV =>
      dsimp [Word.right, Word.rho, Word.proRight]
      rw [← Category.assoc,
        ihU ⟨h.2.2.1, h.2.1, h.2.2.2.1⟩ ⟨h'.2.2.1, h'.2.1, h'.2.2.2.1⟩,
        Category.assoc, ← U.proRight.map_comp,
        ihV ⟨h.1, h.2.2.1, h.2.2.2.2⟩ ⟨h'.1, h'.2.2.1, h'.2.2.2.2⟩,
        U.proRight.map_comp, Category.assoc]

private theorem paste_naturality
    {X Y : Over (Spec (.of P.field.k))} {U V : Word P X Y} (D : Paste U V)
    {J J' : DerivedCategory.Plus (Sheaf X.left.smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient))} (b : J ⟶ J') :
    U.leftPlus.map b ≫ D.etaleMap J' = D.etaleMap J ≫ V.leftPlus.map b := by
  induction D with
  | identity W => simp [Paste.etaleMap]
  | refinement s t r =>
      let := s.quasiCompact
      exact (Etale.rightDerivedLowerShriekOfCompactificationPlusRefinementIso
        P.Coefficient r).inv.naturality b
  | compositor s t v =>
      let := s.quasiCompact
      let := t.quasiCompact
      exact (coherenceEtaleCompositor P.Coefficient s.c t.c v.c).hom.naturality b
  | vertical D E ihD ihE =>
      dsimp [Paste.etaleMap]
      rw [← Category.assoc, ihD, Category.assoc, ihE, ← Category.assoc]
  | before W D ih => exact ih (W.leftPlus.map b)
  | after D W ih =>
      simpa only [Word.leftPlus, Paste.etaleMap, Functor.comp_map, Functor.map_comp]
        using congrArg W.leftPlus.map (ih b)
  | associator U V W => simp [Paste.etaleMap, Word.leftPlus]
  | leftUnitor W => simp [Paste.etaleMap, Word.leftPlus]
  | rightUnitor W => simp [Paste.etaleMap, Word.leftPlus]

private theorem conjugate_transpose
    {X Y : Over (Spec (.of P.field.k))} {U V : Word P X Y} (D : Paste U V)
    (J : DerivedCategory.Plus (Sheaf X.left.smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient)))
    (K : DerivedCategory (Sheaf Y.left.smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient))) (hV : V.Admissible K)
    (z : (V.leftPlus.obj J).obj ⟶ K) :
    U.homEquiv J K ((D.etaleMap J).hom ≫ z) =
      V.homEquiv J K z ≫ D.etaleConjugate K hV := by
  let b : J ⟶ ⟨V.right.obj K, hV.2.1⟩ :=
    ObjectProperty.homMk (V.homEquiv J K z)
  have hz : (V.leftPlus.map b).hom ≫ V.counit K hV = z := by
    apply (V.homEquiv J K).injective
    rw [hom_left]
    simp [Word.counit, b]
  rw [← hz, ← Category.assoc]
  have hn := congrArg (fun t ↦ t.hom) (paste_naturality D b)
  change (U.leftPlus.map b).hom ≫ (D.etaleMap _).hom =
    (D.etaleMap J).hom ≫ (V.leftPlus.map b).hom at hn
  erw [← hn, Category.assoc, hom_left]
  rw [hz]
  rfl

private def etaleRightMap {X Y : Over (Spec (.of P.field.k))} {U V : Word P X Y}
    (D : Paste U V) :
    ∀ (K : DerivedCategory (Sheaf Y.left.smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient)))
    (_hU : U.Admissible K) (_hV : V.Admissible K) (_hD : D.IntermediateBounds K),
    V.right.obj K ⟶ U.right.obj K :=
  match D with
  | .identity _ => fun _ _ _ _ ↦ 𝟙 _
  | .refinement s t r => fun K _ hV _ ↦ (Paste.refinement s t r).etaleConjugate K hV
  | .compositor s t v => fun K _ hV _ ↦ (Paste.compositor s t v).etaleConjugate K hV
  | .vertical D E => fun K hU hV hD ↦
      etaleRightMap E K hD.1 hV hD.2.2 ≫ etaleRightMap D K hU hD.1 hD.2.1
  | .before W D => fun K hU hV hD ↦ W.right.map
      (etaleRightMap D K ⟨hU.1, hU.2.2.1, hU.2.2.2.2⟩
        ⟨hV.1, hV.2.2.1, hV.2.2.2.2⟩ hD)
  | .after D W => fun K hU hV hD ↦
      etaleRightMap D (W.right.obj K) ⟨hU.2.2.1, hU.2.1, hU.2.2.2.1⟩
        ⟨hV.2.2.1, hV.2.1, hV.2.2.2.1⟩ hD
  | .associator _ _ _ => fun _ _ _ _ ↦ 𝟙 _
  | .leftUnitor _ => fun _ _ _ _ ↦ 𝟙 _
  | .rightUnitor _ => fun _ _ _ _ ↦ 𝟙 _

private theorem etale_pasting_transpose
    {X Y : Over (Spec (.of P.field.k))} {U V : Word P X Y} (D : Paste U V)
    (J : DerivedCategory.Plus (Sheaf X.left.smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient)))
    (K : DerivedCategory (Sheaf Y.left.smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient))) (hU : U.Admissible K) (hV : V.Admissible K)
    (hD : D.IntermediateBounds K) (z : (V.leftPlus.obj J).obj ⟶ K) :
    U.homEquiv J K ((D.etaleMap J).hom ≫ z) =
      V.homEquiv J K z ≫ etaleRightMap D K hU hV hD := by
  induction D with
  | identity W =>
      dsimp only [Paste.etaleMap, etaleRightMap]
      simp only [ObjectProperty.FullSubcategory.id_hom, Category.id_comp, Category.comp_id]
  | refinement s t r => exact conjugate_transpose _ J K hV z
  | compositor s t v => exact conjugate_transpose _ J K hV z
  | vertical D E ihD ihE =>
      dsimp [Paste.etaleMap, etaleRightMap]
      rw [Category.assoc,
        ihD J K hU hD.1 hD.2.1,
        ihE J K hD.1 hV hD.2.2, Category.assoc]
  | before W D ih =>
      dsimp [Paste.etaleMap, etaleRightMap, Word.homEquiv, Word.right]
      erw [ih _ K ⟨hU.1, hU.2.2.1, hU.2.2.2.2⟩
        ⟨hV.1, hV.2.2.1, hV.2.2.2.2⟩ hD, hom_right]
      rfl
  | after D W ih =>
      dsimp [Paste.etaleMap, etaleRightMap, Word.homEquiv]
      erw [hom_left, ih J _ ⟨hU.2.2.1, hU.2.1, hU.2.2.2.1⟩
        ⟨hV.2.2.1, hV.2.1, hV.2.2.2.1⟩ hD]
      rfl
  | associator U V W =>
      dsimp only [Paste.etaleMap, etaleRightMap, Word.homEquiv, Equiv.trans_apply]
      simp only [ObjectProperty.FullSubcategory.id_hom, Category.id_comp, Category.comp_id]
      rfl
  | leftUnitor W =>
      dsimp only [Paste.etaleMap, etaleRightMap, Word.homEquiv, Word.leftPlus]
      simp only [ObjectProperty.FullSubcategory.id_hom, Category.id_comp, Category.comp_id,
        Equiv.trans_apply, Functor.id_obj, Functor.comp_obj]
      rfl
  | rightUnitor W =>
      dsimp only [Paste.etaleMap, etaleRightMap, Word.homEquiv, Word.right]
      simp only [ObjectProperty.FullSubcategory.id_hom, Category.id_comp, Category.comp_id,
        Equiv.trans_apply, Functor.id_obj, Functor.comp_obj]
      rfl

private theorem etale_pasting
    {X Y : Over (Spec (.of P.field.k))} {U V : Word P X Y} (D : Paste U V)
    (K : DerivedCategory (Sheaf Y.left.smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient))) (hU : U.Admissible K) (hV : V.Admissible K)
    (hD : D.IntermediateBounds K) :
    D.etaleConjugate K hV = etaleRightMap D K hU hV hD := by
  unfold Paste.etaleConjugate
  rw [etale_pasting_transpose D _ K hU hV hD]
  simp [Word.counit]

private theorem rightMap_comparison
    {X Y : Over (Spec (.of P.field.k))} {U V : Word P X Y} (D : Paste U V)
    (K : DerivedCategory (Sheaf Y.left.smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient))) (hU : U.Admissible K) (hV : V.Admissible K)
    (hD : D.IntermediateBounds K) :
    (coherenceSiteFunctor P.Coefficient X.left).map (etaleRightMap D K hU hV hD) ≫
        (U.rho K hU).hom = (V.rho K hV).hom ≫ D.rightMap K hU hV hD := by
  induction D with
  | identity W =>
      dsimp only [etaleRightMap, Paste.rightMap]
      simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  | refinement s t r => exact conjugate_comparison _ K hU hV
  | compositor s t v => exact conjugate_comparison _ K hU hV
  | vertical D E ihD ihE =>
      dsimp [etaleRightMap, Paste.rightMap]
      rw [Functor.map_comp, Category.assoc, ihD, ← Category.assoc, ihE, Category.assoc]
  | @before A B C W U V D ih =>
      dsimp only [etaleRightMap, Paste.rightMap, Word.rho, Iso.trans_hom,
        Functor.mapIso_hom]
      have hr := rho_naturality W
        ⟨hV.2.2.1, hV.2.1, hV.2.2.2.1⟩
        ⟨hU.2.2.1, hU.2.1, hU.2.2.2.1⟩
        (etaleRightMap D K ⟨hU.1, hU.2.2.1, hU.2.2.2.2⟩
          ⟨hV.1, hV.2.2.1, hV.2.2.2.2⟩ hD)
      erw [← Category.assoc, hr, Category.assoc, ← W.proRight.map_comp,
        ih K ⟨hU.1, hU.2.2.1, hU.2.2.2.2⟩
          ⟨hV.1, hV.2.2.1, hV.2.2.2.2⟩ hD,
        W.proRight.map_comp, Category.assoc]
  | after D W ih =>
      dsimp [etaleRightMap, Paste.rightMap, Word.rho]
      rw [← Category.assoc, ih, Category.assoc]
      simp only [← Functor.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
        Category.id_comp, Category.assoc]
  | associator U V W =>
      dsimp only [etaleRightMap, Paste.rightMap, Word.rho, Word.proRight]
      simp only [Iso.trans_hom, Functor.mapIso_hom, Functor.comp_obj, Functor.comp_map,
        CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id, Functor.map_comp,
        Category.assoc]
      rfl
  | leftUnitor W =>
      dsimp only [etaleRightMap, Paste.rightMap, Word.rho, Word.proRight, Word.right]
      simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.refl_hom, Functor.comp_obj, Functor.id_obj,
        Functor.id_map, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  | rightUnitor W =>
      dsimp only [etaleRightMap, Paste.rightMap, Word.rho, Word.proRight, Word.right]
      simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.refl_hom, Functor.comp_obj, Functor.id_obj,
        CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

/-- Bounded site comparison identifies the actual conjugates and preserves every finite
compatible composition/refinement paste, including identity comparisons and the canonical
composite-adjunction associators. The compositor and refinement displayed in the node
are obtained by the corresponding constructors of Paste.

Source: blueprint lem-pur-co-smooth-etale-locality, proof Step 3, transitive ordinary
counits; thm-pur-composition-coherence, proof Steps 1--2; Stacks Tags 0B65 and 0DV0
(blueprint: lem-pur-bounded-site-compositor-conjugates).

Proof:
1. A compactification over a finite-type k-scheme has a finite nonnegative dimension
bound (lem-kun-dimension-finite-type), with bound zero for the empty scheme. The
chain-supremum dimensions def-kun-dimension and def-kun-topological-krull-dimension
are the ones used in boundedSiteAdjunctionTranspose. Apply that node to every stage.
It gives the normalized counit equation epsilon_p F_p(a) B = C(epsilon_e) and the
compatible transpose equation on precisely the bounded etale-origin witnesses.
2. For the compositor put J = G_h^e K and P = G_g^e K. Site coherence gives
alpha_p (F_g^p B_f) B_g = B_h C(alpha_e). Naturality and Step 1 imply that the
counit-compositor arrows z_p and z_e satisfy z_p (F_g^p B_f) B_g = C(z_e).
These are the chosen compositors, not arbitrary isomorphisms.
3. Transpose first through g. The source F_f^p C_X J has bounded etale witness
F_f^e J via B_f. Source naturality gives u_p B_f = a_g C_Y(u_e).
Remove a_g using its inverse, then transpose through f at the etale target P.
4. Target naturality restores G_f^p(a_g). The composite Hom bijection is transposition
through g then f (def-weil-pbc-composite-adjunction). The counit definition of conjugate
(def-weil-pbc-adjunction-conjugate) identifies the etale transpose with t_e and the
pro-etale one with a_h followed by t_p. This gives the compositor equality.
5. For refinement c to c', put J = G_c'^e K. The refinement square is
r_p B_c = B_c' C(r_e). Naturality and the normalized c' counit give compatible
counit-refinement arrows. Transpose through c. The result is C(q_e) a_c = a_c' q_p,
which is precisely the contravariant refinement equality.
6. The identity comparison followed by the counit transposes to the identity. The
identity adjunction has identity Hom bijection and counit; hence inserting an identity
word inserts only its canonical unitor.
7. Induct on words. For a composite first transpose through its last word, use the
boundary B of its first word as source witness, remove the last comparison, and apply
the induction hypothesis. Restore the last comparison by target naturality, exactly
as in Steps 3--4. The recursive Hom bijection is Adjunction.comp; reassociating it
only reassociates function composition, giving the canonical adjunction associators.
8. Induct on the pasted diagram. Apply Step 7 to its source and target words and use
the target-word counit. The left site-coherence square comes from
lem-pur-compact-support-site-coherence. For vertical paste conjugates reverse; for
horizontal paste they whisker, as in lem-weil-pbc-mate-pasting clauses 1--3. On the
pro-etale side expand only the witnessed Hom bijections: adjacent units and counits
cancel by the triangle equations. Injectivity identifies the conjugate of the entire
left paste with rightMap. This includes mixed pastes, further refinements, units and
reassociations. Every intermediate object is one of the recorded bounded witnesses.
-/
theorem boundedSiteCompositorConjugates
    {X Y : Over (Spec (.of P.field.k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    {U V : Word P X Y} (D : Paste U V)
    (K : DerivedCategory.Plus (Sheaf Y.left.smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient)))
    (hU : U.Admissible K.obj) (hV : V.Admissible K.obj)
    (hD : D.IntermediateBounds K.obj) :
    D.proConjugate K.obj hV = D.rightMap K.obj hU hV hD ∧
      (coherenceSiteFunctor P.Coefficient X.left).map (D.etaleConjugate K.obj hV) ≫
          (U.rho K.obj hU).hom =
        (V.rho K.obj hV).hom ≫ D.rightMap K.obj hU hV hD := by
  have hp := rightMap_comparison D K.obj hU hV hD
  rw [← etale_pasting D K.obj hU hV hD] at hp
  refine ⟨?_, hp⟩
  apply (cancel_epi (V.rho K.obj hV).hom).mp
  rw [← conjugate_comparison D K.obj hU hV]
  exact hp

end AlgebraicGeometry.ProEtale.BoundedSiteConjugates
