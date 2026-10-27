/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q73
-/
module

public import Sheaf.AlgebraicGeometry.OrdinaryTowerCartesianMap
public import Sheaf.AlgebraicGeometry.CodimensionResolutionPrefix
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.Compactification.StrictTransform
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.RingTheory.KrullDimension.Basic
import Sheaf.TraceFormula.ReducedSchemeImage
import Sheaf.AlgebraicGeometry.ReducedNoetherianBlowupGeometry
import WeilConjectures.Blowup.Proper
import WeilConjectures.Blowup.FlatBaseChange
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Sheaf.AlgebraicGeometry.FlatMaximalDominanceBaseChange
import WeilConjectures.Compactification.StrictTransformBlowup
import Mathlib.RingTheory.Flat.Localization
import Mathlib.Topology.NoetherianSpace

/-! # Globalizing synchronized local ordinary blowup towers

Source: Temkin, Functorial desingularization of quasi-excellent schemes in characteristic
zero: the non-embedded case, arXiv:0904.1592v2, sections 2.1.5--2.1.6, 2.2.1--2.2.8,
Lemma 2.2.1, section 4.2.1 and Lemmas 4.2.4--4.2.5
(blueprint: lem-per-local-blowup-tower-globalization).

The existing ordinary towers and their cartesian maps retain every center ideal and
empty stage. The auxiliary records below specify the closure and ambient comparisons;
they do not choose a tower from an existence theorem. Flat pullback uses full ideals.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The disjoint union of the local base changes of a scheme over a set of base points.
Source: Temkin 2.1.5 and 2.2.6; the local schemes are spectra of the actual stalks
(blueprint: lem-per-local-blowup-tower-globalization). -/
def Scheme.localSpectrumPullback {X P : Scheme.{u}} (p : P ⟶ X) (S : Set X) : Scheme.{u} :=
  ∐ fun s : S ↦ pullback p (X.fromSpecStalk s.1)

/-- The canonical map from the disjoint union of local base changes to the original scheme.
Source: Temkin 2.1.5 and 2.2.6
(blueprint: lem-per-local-blowup-tower-globalization). -/
def Scheme.localSpectrumPullbackMap {X P : Scheme.{u}} (p : P ⟶ X) (S : Set X) :
    Scheme.localSpectrumPullback p S ⟶ P :=
  Sigma.desc fun s : S ↦ pullback.fst p (X.fromSpecStalk s.1)

/-- Generic points of the inverse image of a closed support, as points of the base.
Source: Temkin 2.1.6 and 4.2.4, generic-local reconstruction
(blueprint: lem-per-local-blowup-tower-globalization). -/
def Scheme.genericSupportPoints {X Y : Scheme.{u}} (f : Y ⟶ X) (Z : Set X) : Set Y :=
  {y | ∃ hy : y ∈ f ⁻¹' Z, (⟨y, hy⟩ : f ⁻¹' Z) ∈ genericPoints (f ⁻¹' Z)}

namespace OrdinaryBlowupTower

/-- A globalization retains the local tower, with its original length, and its centers
are exactly the schematic images of the local centers. The pushforward of an ideal is
`(I.subschemeι ≫ j).ker`, so this is the smallest closed subscheme, with its full ideal.
Source: Temkin 2.2.6, Lemma 2.2.1
(blueprint: lem-per-local-blowup-tower-globalization). -/
structure LocalClosure {X P : Scheme.{u}} (p : P ⟶ X) (S : Set X)
    (L : OrdinaryBlowupTower (Scheme.localSpectrumPullback p S))
    (G : OrdinaryBlowupTower P)
    extends OrdinaryTowerCartesianMap (Scheme.localSpectrumPullbackMap p S) G L where
  closure_center : ∀ i : Fin L.length,
    G.center (Fin.cast length_eq i) = (L.center i).map (map i.castSucc)

/-- Reconstructing a tower's centers from the local schemes recovers the exact original
ideals. Thus subsequent ordinary blowups are determined, including unit-ideal stages.
Source: Temkin 2.1.6 and Lemma 2.2.1
(blueprint: lem-per-local-blowup-tower-globalization). -/
def RecoveredFromLocalSpectra {X P : Scheme.{u}} (p : P ⟶ X) (S : Set X)
    (G : OrdinaryBlowupTower P) : Prop :=
  ∀ i : Fin G.length,
    ((G.center i).comap (Scheme.localSpectrumPullbackMap (G.toBase i.castSucc ≫ p) S)).map
      (Scheme.localSpectrumPullbackMap (G.toBase i.castSucc ≫ p) S) = G.center i

/-- The inverse images of the specified base points are schematically dense in every
center. The actual local-center schemes are used, without reducing their ideals.
Source: Temkin 2.1.6
(blueprint: lem-per-local-blowup-tower-globalization). -/
def CentersSchematicallyDenseOver {X P : Scheme.{u}} (p : P ⟶ X) (S : Set X)
    (G : OrdinaryBlowupTower P) : Prop :=
  ∀ i : Fin G.length, IsSchemeTheoreticallyDominant
    (Scheme.localSpectrumPullbackMap (G.centerToBase i ≫ p) S)

/-- An ambient realization blows up the same closed centers and identifies the intrinsic
levels with the successive strict transforms. Both projections of each strict transform
are specified; in particular an arbitrary isomorphism of the resulting schemes will not do.
Source: Temkin 4.2.1 and Lemma 4.2.1; Stacks Tag 080E
(blueprint: lem-per-local-blowup-tower-globalization). -/
structure AmbientLift {P M : Scheme.{u}} (G : OrdinaryBlowupTower P) (j : P ⟶ M) where
  tower : OrdinaryBlowupTower M
  length_eq : G.length = tower.length
  inclusion : ∀ i : Fin (G.length + 1),
    G.level i ⟶ tower.level (Fin.cast (congrArg Nat.succ length_eq) i)
  closed : ∀ i, IsClosedImmersion (inclusion i)
  initial : inclusion 0 ≫ tower.initial.hom = G.initial.hom ≫ j
  arrows : ∀ i j' (hij : i ≤ j'),
    G.transition i j' hij ≫ inclusion i = inclusion j' ≫
      tower.transition (Fin.cast (congrArg Nat.succ length_eq) i)
        (Fin.cast (congrArg Nat.succ length_eq) j') hij
  center : ∀ i : Fin G.length,
    tower.center (Fin.cast length_eq i) = (G.center i).map (inclusion i.castSucc)
  center_restrict : ∀ i : Fin G.length,
    (tower.center (Fin.cast length_eq i)).comap (inclusion i.castSucc) = G.center i
  strictIso : ∀ i : Fin G.length, G.level i.succ ≅
    (tower.center (Fin.cast length_eq i)).strictTransform (inclusion i.castSucc)
  strict_toSource : ∀ i : Fin G.length,
    (strictIso i).hom ≫ strictTransformToSource (inclusion i.castSucc)
      (tower.center (Fin.cast length_eq i)).blowupMap
      (tower.center (Fin.cast length_eq i)).support.compl =
        G.transition i.castSucc i.succ (le_of_lt i.castSucc_lt_succ)
  strict_toAmbient : ∀ i : Fin G.length,
    (strictIso i).hom ≫ strictTransformMap (inclusion i.castSucc)
      (tower.center (Fin.cast length_eq i)).blowupMap
      (tower.center (Fin.cast length_eq i)).support.compl =
        inclusion i.succ ≫ (tower.blowupIso (Fin.cast length_eq i)).hom

/-- Exact reconstruction includes an uncontracted restriction of the tower and equality
of all ideals obtained by taking schematic images of its locally restricted centers.
Source: Temkin 2.1.6 and Lemma 2.2.1
(blueprint: lem-per-local-blowup-tower-globalization). -/
def LocalReconstruction {X P : Scheme.{u}} (p : P ⟶ X) (S : Set X)
    (G : OrdinaryBlowupTower P) : Prop :=
  RecoveredFromLocalSpectra p S G ∧
    ∃ L : OrdinaryBlowupTower (Scheme.localSpectrumPullback p S), Nonempty (LocalClosure p S L G)

/-- The full local center is pulled back before its schematic image is taken. The
resulting ideal is the extended global ideal, with no radical operation.
Source: Temkin 4.2.4, Lemma 4.2.5; Stacks Tag 081I
(blueprint: lem-per-local-blowup-tower-globalization). -/
def FullCenterImageBaseChange {X U T X' : Scheme.{u}} (q : T ⟶ X)
    (I : U.IdealSheafData) (j : U ⟶ T) (J : T.IdealSheafData) (f : X' ⟶ X) : Prop :=
  (pullback.snd (I.subschemeι ≫ j) (pullback.fst q f)).ker =
    J.comap (pullback.fst q f)

end OrdinaryBlowupTower

open OrdinaryBlowupTower

/-- Synchronized local ordinary blowups globalize by schematic closure, independently
of spreading neighborhoods. Each center has the specified reduced geometry and pure
base codimension; local-center restrictions are schematically dense.

Source: Temkin 2.1.5--2.1.6, 2.2.6, Lemma 2.2.1 and 4.2.3
(blueprint: lem-per-local-blowup-tower-globalization).

Proof (node steps 1--8):
1. Induct over the finite local tower without deleting stages. At a stage T, its maps
   from T_s are flat monomorphisms by localization-flatness and flat base change
   (lem-weil-pbc-localization-flat, lem-weil-pbc-flat-morphism-base-change).
   The local centers and their finite disjoint union D are Noetherian, hence D -> T
   is quasi-compact (pqf-def-locnoeth, def-pc-fibre-product).
2. Take C to be the schematic image of D -> T. The image-kernel theorem identifies
   its ideal with the kernel of restriction of functions. On Noetherian affines the
   ideal and kernels of maps from finite free modules are finitely generated, proving
   coherence (lemma-nagata-scheme-image-ideal-qc, pqf-def-coherent). Reduced-image
   geometry gives reducedness of C (lem-trf-reduced-scheme-image).
3. Pull back to each local base by lem-sfb-scheme-image-flat-base-change. The same
   summand gives its original closed center; the other summands are empty, since a
   member of S cannot generalize another member. Use the image of a closed immersion
   (lemma-nagata-scheme-image-of-closed-immersion) to recover the full local ideal.
4. Blow up C. Flat blowup base change identifies the next local stages, even at empty
   centers (thm-nagata-blowup-flat-base-change). Reducedness and Noetherianity persist
   (lem-per-reduced-noetherian-blowup-geometry); properness of blowups and composition
   keep every stage proper over X (lemma-nagata-blowup-proper,
   lem-weil-pbc-proper-composition). Repeat for all stages.
5. Finite irreducible decomposition and sobriety identify component generic points of
   C with images of local component generic points, which map into S
   (lem-sc-noetherian-finite-irreducible-components, lem-sc-scheme-sober).
6. Properness makes the base image closed, hence it is precisely the union of the
   closures of its active members of S. Incomparability gives its component generic
   points and the assumed codimension r. The image-kernel injection proves schematic
   density of its restrictions over those points (def-weil-proper-morphism,
   lemma-nagata-scheme-image-ideal-qc).
7. If C contained an open in T, it would contain a generic point of a component of T.
   That component would be a component of C and its generic point would map into S.
   Localizing there produces a component of T_s contained in its given center,
   contradicting local nowhere-density (lem-sc-irreducible-components-cover,
   lem-sc-scheme-sober, lem-sc-noetherian-finite-irreducible-components).
8. Every schematic closure has the same kernel ideal. Induction and the universal
   property of each blowup give the unique center-preserving comparison, proving
   independence of auxiliary neighborhoods (def-nagata-scheme-theoretic-image,
   lemma-nagata-scheme-image-ideal-qc). No arbitrary extra components may be added.
-/
theorem exists_localBlowupTower_globalization {X P : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian P] [IsReduced P] (p : P ⟶ X) [IsProper p]
    (S : Set X) (hS : S.Finite)
    (hinc : S.Pairwise (fun s t ↦ ¬ s ⤳ t ∧ ¬ t ⤳ s))
    (r : ℕ) (hr : 1 ≤ r)
    (hdim : ∀ s ∈ S, ringKrullDim (X.presheaf.stalk s) = (r : WithBot ℕ∞))
    (L : OrdinaryBlowupTower (Scheme.localSpectrumPullback p S))
    (hcoh : ∀ i : Fin L.length,
      RingedSpace.IsCoherent (L.level i.castSucc).toRingedSpace (L.center i).toModules)
    (hred : ∀ i : Fin L.length, IsReduced (L.center i).subscheme)
    (hnd : ∀ i : Fin L.length, IsNowhereDense ((L.center i).support : Set (L.level i.castSucc)))
    (hsupp : ∀ i : Fin L.length,
      Set.range (L.centerToBase i ≫ Scheme.localSpectrumPullbackMap p S ≫ p) ⊆ S) :
    ∃ G : OrdinaryBlowupTower P, Nonempty (LocalClosure p S L G) ∧
      (∀ i : Fin G.length,
        RingedSpace.IsCoherent (G.level i.castSucc).toRingedSpace (G.center i).toModules ∧
        IsReduced (G.center i).subscheme ∧
        IsNowhereDense ((G.center i).support : Set (G.level i.castSucc)) ∧
        Set.range (G.centerToBase i ≫ p) =
          ⋃ s ∈ S ∩ Set.range (G.centerToBase i ≫ p), closure ({s} : Set X) ∧
        (∀ z : Set.range (G.centerToBase i ≫ p),
          z ∈ genericPoints (Set.range (G.centerToBase i ≫ p)) →
            ringKrullDim (X.presheaf.stalk z.1) = (r : WithBot ℕ∞))) ∧
      CentersSchematicallyDenseOver p S G ∧
      (∀ H : OrdinaryBlowupTower P, LocalClosure p S L H →
        Nonempty (OrdinaryTowerCartesianMap (𝟙 P) G H) ∧
          Subsingleton (OrdinaryTowerCartesianMap (𝟙 P) G H)) := by
  sorry

/-- The same closure centers can be blown up in any Noetherian ambient scheme in
which P is closed, with all successive strict transforms identified over both factors.

Source: Temkin 4.2.1, Lemma 4.2.1; Stacks Tag 080E
(blueprint: lem-per-local-blowup-tower-globalization).

Proof (node step 9): induct over the ordered centers. The maps from the local centers
factor through the current closed intrinsic stage. The kernel of A -> B -> O_D is
its inverse-image ideal in A, so their ambient schematic image is the intrinsic
closure center with its composite closed immersion
(lemma-nagata-scheme-image-ideal-qc, def-weil-closed-immersion).
The strict-transform-is-blowup theorem identifies the next intrinsic blowup with
its strict transform in the ambient blowup, compatibly with both projections
(thm-nagata-strict-transform-is-blowup). Iterate, including all empty stages. -/
theorem localBlowupTower_globalization_ambient {X P M : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian P] [IsReduced P] [IsNoetherian M]
    (p : P ⟶ X) [IsProper p] (S : Set X) (hS : S.Finite)
    (hinc : S.Pairwise (fun s t ↦ ¬ s ⤳ t ∧ ¬ t ⤳ s))
    (r : ℕ) (hr : 1 ≤ r)
    (hdim : ∀ s ∈ S, ringKrullDim (X.presheaf.stalk s) = (r : WithBot ℕ∞))
    (L : OrdinaryBlowupTower (Scheme.localSpectrumPullback p S))
    (G : OrdinaryBlowupTower P) (c : LocalClosure p S L G)
    (hcoh : ∀ i : Fin L.length,
      RingedSpace.IsCoherent (L.level i.castSucc).toRingedSpace (L.center i).toModules)
    (hred : ∀ i : Fin L.length, IsReduced (L.center i).subscheme)
    (hnd : ∀ i : Fin L.length,
      IsNowhereDense ((L.center i).support : Set (L.level i.castSucc)))
    (hsupp : ∀ i : Fin L.length,
      Set.range (L.centerToBase i ≫ Scheme.localSpectrumPullbackMap p S ≫ p) ⊆ S)
    (j : P ⟶ M) [IsClosedImmersion j] (m : M ⟶ X) (hp : j ≫ m = p) :
    Nonempty (AmbientLift G j) := by
  sorry

/-- Flat pullback of the globalization uses full pulled-back local centers and exact
extended ideals. Reconstruction from the new generic local bases is conditional on
schematic density; reduced pulled-back centers suffice for that condition.

Source: Temkin 2.2.5, 4.2.4, Lemma 4.2.5 and 2.1.6; Stacks Tags 081I and 0805
(blueprint: lem-per-local-blowup-tower-globalization).

Proof (node steps 10--12):
10. Flat base change of schematic images identifies the image of the full pulled-back
    local center with the extended global ideal (lem-sfb-scheme-image-flat-base-change,
    lem-weil-pbc-flat-morphism-base-change). Flat blowup base change identifies the next
    stages (thm-nagata-blowup-flat-base-change). Induct without reducing any ideal.
11. Under the displayed density condition, the local-center restriction has the same
    kernel as the pulled-back center. Taking its image therefore recovers that center
    (lemma-nagata-scheme-image-ideal-qc). Inductively blow up these same ideals.
12. If pulled-back centers are reduced, their generic points map to generic points of
    the pulled-back base image by lem-per-flat-maximal-dominance-base-change. They
    therefore lie above the selected set S'. The local restriction is topologically
    dense. It is quasi-compact since the finite local source is Noetherian. The reduced
    dense-image criterion makes it schematically dense
    (lemma-nagata-reduced-dense-image-schematic, lem-trf-reduced-scheme-image).
Only unit-ideal stages may be removed; the uncontracted comparison removes none.
There is no reducedness or codimension-preservation assertion for general flat maps.
-/
theorem localBlowupTower_globalization_flat {X P X' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian P] [IsReduced P]
    (p : P ⟶ X) [IsProper p] (S : Set X) (hS : S.Finite)
    (hinc : S.Pairwise (fun s t ↦ ¬ s ⤳ t ∧ ¬ t ⤳ s))
    (r : ℕ) (hr : 1 ≤ r)
    (hdim : ∀ s ∈ S, ringKrullDim (X.presheaf.stalk s) = (r : WithBot ℕ∞))
    (L : OrdinaryBlowupTower (Scheme.localSpectrumPullback p S))
    (G : OrdinaryBlowupTower P) (c : LocalClosure p S L G)
    (hcoh : ∀ i : Fin L.length,
      RingedSpace.IsCoherent (L.level i.castSucc).toRingedSpace (L.center i).toModules)
    (hred : ∀ i : Fin L.length, IsReduced (L.center i).subscheme)
    (hnd : ∀ i : Fin L.length,
      IsNowhereDense ((L.center i).support : Set (L.level i.castSucc)))
    (hsupp : ∀ i : Fin L.length,
      Set.range (L.centerToBase i ≫ Scheme.localSpectrumPullbackMap p S ≫ p) ⊆ S)
    [IsNoetherian X'] (f : X' ⟶ X) [Flat f] :
    ∃ B : OrdinaryBlowupTower (pullback p f),
      Nonempty (OrdinaryTowerCartesianMap (pullback.fst p f) G B) ∧
      (∀ i : Fin L.length, FullCenterImageBaseChange
        (G.toBase (Fin.cast c.length_eq i).castSucc ≫ p)
        (L.center i) (c.map i.castSucc) (G.center (Fin.cast c.length_eq i)) f) ∧
      (∃ C : OrdinaryBlowupTower (pullback p f),
        Nonempty (OrdinaryResolutionComparison (pullback.fst p f) G C)) ∧
      (∀ (S' : Set X') (_ : S'.Finite),
        S' = Scheme.genericSupportPoints f (closure S) →
          (CentersSchematicallyDenseOver (pullback.snd p f) S' B →
            LocalReconstruction (pullback.snd p f) S' B) ∧
          ((∀ i : Fin B.length, IsReduced (B.center i).subscheme) →
            CentersSchematicallyDenseOver (pullback.snd p f) S' B)) := by
  sorry

/-- Ambient globalization commutes with flat base change as a tower of actual ideals
and strict transforms. Reconstruction from new generic local bases has the same density
qualification as intrinsic reconstruction. The comparison keeps every original stage.

Source: Temkin 4.2.1--4.2.4, Lemma 4.2.5; Stacks Tags 081I, 0805 and 080E
(blueprint: lem-per-local-blowup-tower-globalization).

Proof (node steps 9--12): at each ambient stage the schematic image of the local
center is its intrinsic image followed by the closed intrinsic inclusion. This follows
from the inverse-image kernel calculation in step 9
(lemma-nagata-scheme-image-ideal-qc, def-weil-closed-immersion).
Flat base change of schematic images retains exactly this ideal, and flat blowup base
change retains the ambient stages (lem-sfb-scheme-image-flat-base-change,
thm-nagata-blowup-flat-base-change). The strict-transform-is-blowup theorem identifies
the intrinsic stages and both their projections
(thm-nagata-strict-transform-is-blowup). Inductively these comparisons commute with
the closed inclusions. For generic-local reconstruction, density in the intrinsic
center gives the identical ambient image ideal by composition with the closed
immersion. If the pulled-back centers are reduced, maximal dominance under flat base
change makes their local restrictions topologically dense, and the reduced-dense-image
criterion gives schematic density (lem-per-flat-maximal-dominance-base-change,
lemma-nagata-reduced-dense-image-schematic). All ideals and empty stages are retained;
nonempty Cartier-center isomorphisms are never contracted.
-/
theorem localBlowupTower_globalization_ambient_flat {X P M X' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian P] [IsReduced P] [IsNoetherian M]
    (p : P ⟶ X) [IsProper p] (m : M ⟶ X) (j : P ⟶ M) [IsClosedImmersion j]
    (hp : j ≫ m = p) (S : Set X) (hS : S.Finite)
    (hinc : S.Pairwise (fun s t ↦ ¬ s ⤳ t ∧ ¬ t ⤳ s))
    (r : ℕ) (hr : 1 ≤ r)
    (hdim : ∀ s ∈ S, ringKrullDim (X.presheaf.stalk s) = (r : WithBot ℕ∞))
    (L : OrdinaryBlowupTower (Scheme.localSpectrumPullback p S))
    (G : OrdinaryBlowupTower P) (c : LocalClosure p S L G) (A : AmbientLift G j)
    (hcoh : ∀ i : Fin L.length,
      RingedSpace.IsCoherent (L.level i.castSucc).toRingedSpace (L.center i).toModules)
    (hred : ∀ i : Fin L.length, IsReduced (L.center i).subscheme)
    (hnd : ∀ i : Fin L.length,
      IsNowhereDense ((L.center i).support : Set (L.level i.castSucc)))
    (hsupp : ∀ i : Fin L.length,
      Set.range (L.centerToBase i ≫ Scheme.localSpectrumPullbackMap p S ≫ p) ⊆ S)
    [IsNoetherian X'] (f : X' ⟶ X) [Flat f] :
    ∃ (B : OrdinaryBlowupTower (pullback p f))
      (b : OrdinaryTowerCartesianMap (pullback.fst p f) G B)
      (A' : AmbientLift B (pullback.map p f m f j (𝟙 X') (𝟙 X)
        ((Category.comp_id p).trans hp.symm)
        ((Category.comp_id f).trans (Category.id_comp f).symm)))
      (a : OrdinaryTowerCartesianMap (pullback.fst m f) A.tower A'.tower),
      (∀ i : Fin (B.length + 1),
        HEq (A'.inclusion i ≫ a.map (Fin.cast (congrArg Nat.succ A'.length_eq) i))
          (b.map i ≫ A.inclusion (Fin.cast (congrArg Nat.succ b.length_eq) i))) ∧
      (∀ i : Fin L.length, FullCenterImageBaseChange
        (A.tower.toBase
          (Fin.cast A.length_eq (Fin.cast c.length_eq i)).castSucc ≫ m)
        (L.center i)
        (c.map i.castSucc ≫ A.inclusion (Fin.cast c.length_eq i).castSucc)
        (A.tower.center (Fin.cast A.length_eq (Fin.cast c.length_eq i))) f) ∧
      (∃ C : OrdinaryBlowupTower (pullback m f),
        Nonempty (OrdinaryResolutionComparison (pullback.fst m f) A.tower C)) ∧
      (∀ (S' : Set X') (_ : S'.Finite),
        S' = Scheme.genericSupportPoints f (closure S) →
          (CentersSchematicallyDenseOver (pullback.snd p f) S' B →
            LocalReconstruction (pullback.snd p f) S' B ∧
              LocalReconstruction (pullback.snd m f) S' A'.tower) ∧
          ((∀ i : Fin B.length, IsReduced (B.center i).subscheme) →
            CentersSchematicallyDenseOver (pullback.snd p f) S' B)) := by
  sorry

end AlgebraicGeometry
