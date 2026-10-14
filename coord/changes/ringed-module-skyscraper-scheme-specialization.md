# Ringed and scheme module skyscrapers

## Reason

Upstream review #1428 requests that ringed-space and scheme skyscrapers use one
construction. Keep the general ringed-space implementation and make the scheme
constructor specialize it. Arbitrary ringed spaces cannot be cast to schemes.

The generic abelian presheaf helper has no module hypothesis, preserving the
scheme API's existing omission of scalar structure in its additive section and
sheafness declarations. Scalar action in both APIs is still the same germ action.
The existing scheme declarations keep the `def` keyword as required by the
adaptation signature/visibility guard, with alias bodies rather than duplicate data.

This is an explicitly requested duplicate repair, not an adaptation forced by a
compiler failure. The unclaimed source module does not originally import the item.
The delivery tool's counterfactual compiler guard will therefore reject its inclusion
without a repair-specific scope exception; this record does not invent such evidence.

## Old

The original ringed-space variable was `X : RingedSpace.{u_sky}`. Its original
bundled signatures already force the carrier universe to equal `u_sky`.

### Sheaf.Topology.RingedModuleSkyscraper

```lean
abbrev RingedSkyscraperSections (M : ModuleCat.{u_sky} (X.presheaf.stalk x)) (V : Opens X) : Type u_sky := PLift (x ∈ V) → M

abbrev ringedSkyscraperPresheafAb (M : ModuleCat.{u_sky} (X.presheaf.stalk x)) : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u_sky} where obj V := AddCommGrpCat.of (RingedSkyscraperSections X x M V.unop) map f := AddCommGrpCat.ofHom { toFun := fun s h ↦ s ⟨f.unop.le h.down⟩ map_zero' := rfl map_add' := fun _ _ ↦ rfl } map_id _ := rfl map_comp _ _ := rfl

theorem ringedSkyscraperPresheafAb_isSheaf (M : ModuleCat.{u_sky} (X.presheaf.stalk x)) : Presheaf.IsSheaf (Opens.grothendieckTopology X) (ringedSkyscraperPresheafAb X x M) := by classical apply (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing (X := X.carrier) (ringedSkyscraperPresheafAb X x M)).mpr intro ι U sf hsf choose index index_spec using fun h : PLift (x ∈ iSup U) ↦ Opens.mem_iSup.mp h.down let s : RingedSkyscraperSections X x M (iSup U) := fun h ↦ sf (index h) ⟨index_spec h⟩ refine ⟨s, ?_, ?_⟩ · intro i funext h exact congrFun (hsf (index ⟨(Opens.leSupr U i).le h.down⟩) i) ⟨⟨index_spec ⟨(Opens.leSupr U i).le h.down⟩, h.down⟩⟩ · intro t ht funext h exact congrFun (ht (index h)) ⟨index_spec h⟩
```

### WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk

```lean
def SkyscraperSections (V : X.Opens) : Type u := PLift (x ∈ V) → I

def skyscraperPresheafAb : X.Opensᵒᵖ ⥤ Ab.{u} where obj V := AddCommGrpCat.of (SkyscraperSections x I V.unop) map i := AddCommGrpCat.ofHom { toFun s hx := s ⟨i.unop.le hx.down⟩ map_zero' := rfl map_add' _ _ := rfl } map_id _ := rfl map_comp _ _ := rfl

lemma isSheaf_skyscraperPresheafAb : Presheaf.IsSheaf (Opens.grothendieckTopology X) (skyscraperPresheafAb x I) := by rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (CategoryTheory.forget Ab.{u}), isSheaf_iff_isSheaf_of_type] intro U S hS s hs -- have key {V W : X.Opens} (f : V ⟶ U) (g : W ⟶ U) (hf : S f) (hg : S g) (hV : x ∈ V) (hW : x ∈ W) : s f hf ⟨hV⟩ = s g hg ⟨hW⟩ := by have := hs (homOfLE (inf_le_left : V ⊓ W ≤ V)) (homOfLE inf_le_right) hf hg (Subsingleton.elim _ _) exact congr_arg (fun t : SkyscraperSections x I (V ⊓ W) ↦ t ⟨⟨hV, hW⟩⟩) this choose V f hf hV using hS refine ⟨show SkyscraperSections x I U from fun hx ↦ s (f x hx.down) (hf x hx.down) ⟨hV x hx.down⟩, fun W g hg ↦ ?_, fun t ht ↦ ?_⟩ · refine SkyscraperSections.ext fun hx ↦ ?_ exact key _ _ _ _ _ _ · refine SkyscraperSections.ext fun hx ↦ ?_ exact congr_arg (fun t : SkyscraperSections x I (V x hx) ↦ t ⟨hV x hx⟩) (ht (f x hx) (hf x hx))

def skyscraper : X.Modules where val := PresheafOfModules.ofPresheaf (skyscraperPresheafAb x I) fun _ _ i a s ↦ skyscraperPresheafAb_map_smul x I i a s isSheaf := isSheaf_skyscraperPresheafAb x I
```

## New

The variable is written explicitly as `X : RingedSpace.{u_sky, u_sky}`, with the
same elaborated universes for every surviving declaration. The scheme module adds
`public import Sheaf.Topology.RingedModuleSkyscraper` for its definitions.

### Sheaf.Topology.RingedModuleSkyscraper

```lean
abbrev ringedSkyscraperSectionsType (I : Type u_sky) (V : Opens X) : Type u_sky := PLift (x ∈ V) → I

abbrev ringedSkyscraperPresheafAbOfType (I : Type u_sky) [AddCommGroup I] : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u_sky} where obj V := AddCommGrpCat.of (ringedSkyscraperSectionsType X x I V.unop) map f := AddCommGrpCat.ofHom { toFun := fun s h ↦ s ⟨f.unop.le h.down⟩ map_zero' := rfl map_add' := fun _ _ ↦ rfl } map_id _ := rfl map_comp _ _ := rfl

theorem ringedSkyscraperPresheafAbOfType_isSheaf (I : Type u_sky) [AddCommGroup I] : Presheaf.IsSheaf (Opens.grothendieckTopology X) (ringedSkyscraperPresheafAbOfType X x I) := by classical apply (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing (X := X.carrier) (ringedSkyscraperPresheafAbOfType X x I)).mpr intro ι U sf hsf choose index index_spec using fun h : PLift (x ∈ iSup U) ↦ Opens.mem_iSup.mp h.down let s : ringedSkyscraperSectionsType X x I (iSup U) := fun h ↦ sf (index h) ⟨index_spec h⟩ refine ⟨s, ?_, ?_⟩ · intro i funext h exact congrFun (hsf (index ⟨(Opens.leSupr U i).le h.down⟩) i) ⟨⟨index_spec ⟨(Opens.leSupr U i).le h.down⟩, h.down⟩⟩ · intro t ht funext h exact congrFun (ht (index h)) ⟨index_spec h⟩

abbrev RingedSkyscraperSections (M : ModuleCat.{u_sky} (X.presheaf.stalk x)) (V : Opens X) : Type u_sky := ringedSkyscraperSectionsType X x M V

abbrev ringedSkyscraperPresheafAb (M : ModuleCat.{u_sky} (X.presheaf.stalk x)) : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u_sky} := ringedSkyscraperPresheafAbOfType X x M

theorem ringedSkyscraperPresheafAb_isSheaf (M : ModuleCat.{u_sky} (X.presheaf.stalk x)) : Presheaf.IsSheaf (Opens.grothendieckTopology X) (ringedSkyscraperPresheafAb X x M) := ringedSkyscraperPresheafAbOfType_isSheaf X x M
```

### WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk

```lean
def SkyscraperSections (V : X.Opens) : Type u := SheafOfModules.ringedSkyscraperSectionsType X.toRingedSpace x I V

def skyscraperPresheafAb : X.Opensᵒᵖ ⥤ Ab.{u} := SheafOfModules.ringedSkyscraperPresheafAbOfType X.toRingedSpace x I

lemma isSheaf_skyscraperPresheafAb : Presheaf.IsSheaf (Opens.grothendieckTopology X) (skyscraperPresheafAb x I) := SheafOfModules.ringedSkyscraperPresheafAbOfType_isSheaf X.toRingedSpace x I

def skyscraper : X.Modules := SheafOfModules.ringedModuleSkyscraper X.toRingedSpace x (ModuleCat.of _ I)
```

## Users

All existing users continue to refer to the same public names and definitionally
identical section data. No hypotheses, conclusions, binders, or visibility change.
The general constructor still works on opens containing the point, opens missing
the point, empty covers and zero coefficient modules. The target statements are
unchanged. Their semantic review should be reconfirmed for the refactored definitions.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.FlatSheafStalk | unclaimed | Definitionally identical APIs; no adaptation required. |
| Sheaf.AlgebraicGeometry.GlobalGenerationNonvanishingCover | unclaimed | Definitionally identical APIs; no adaptation required. |
| Sheaf.AlgebraicGeometry.ResidueBettiZeroOfTensorVanishing | unclaimed | Definitionally identical APIs; no adaptation required. |
| Sheaf.Paper.ModuleCupGodementAugmentation | unclaimed | Definitionally identical APIs; no adaptation required. |
| Sheaf.Paper.ModuleCupGodementBetaExists | unclaimed | Definitionally identical APIs; no adaptation required. |
| Sheaf.Paper.ModuleCupGodementCodegeneracies | unclaimed | Definitionally identical APIs; no adaptation required. |
| Sheaf.Paper.ModuleCupGodementIteratePairingsCanonicalCollapse | unclaimed | Definitionally identical APIs; no adaptation required. |
| Sheaf.Paper.ModuleCupGodementModel | unclaimed | Definitionally identical APIs; no adaptation required. |
| Sheaf.Paper.ModuleCupGodementObjectFlasque | unclaimed | Definitionally identical APIs; no adaptation required. |
| Sheaf.Paper.ModuleCupGodementPairingsFromBeta | unclaimed | Definitionally identical APIs; no adaptation required. |
| Sheaf.Paper.ModuleCupGodementRelations | unclaimed | Definitionally identical APIs; no adaptation required. |
| Sheaf.Paper.ModuleCupGodementStalkContraction | unclaimed | Definitionally identical APIs; no adaptation required. |
| Sheaf.Paper.ModuleCupGodementTensorCoordinates | unclaimed | Definitionally identical APIs; no adaptation required. |
| Sheaf.Paper.ModuleCupGodementTensorMapOfPairingExists | unclaimed | Definitionally identical APIs; no adaptation required. |
| Sheaf.Topology.RingedModuleSkyscraper | D4 | Provides the shared coefficient-type construction; bundled APIs specialize it. |
| Sheaf.Topology.SkyscraperComplexStalk | unclaimed | Definitionally identical APIs; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk | unclaimed | Definitions forward to the shared ringed-space constructor; all signatures and other proofs preserved. |

## Status

landed 20261014T051231-L-1771808 2026-10-14 (merge of deliver/D4/Sheaf.Topology.RingedModuleSkyscraper)
