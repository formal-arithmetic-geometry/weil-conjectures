# FilteredTwoColimitModel private proof helpers

## Reason

Server preflight classifies the newly added `omit ... in` commands as a textual
interface change and requests this record. Each command scopes only a new private,
proved theorem: it prevents unused directedness and nonemptiness assumptions from
being included in that helper. No existing public signature, definition, instance,
visibility, section variable, or public import changes. All 15 existing holes are
proved. No target meaning changes and no consumer adaptation is necessary.

## Old

There are no corresponding private declarations in the original module. Its
section command, retained verbatim, is:

```lean
variable [IsDirected I (· ≤ ·)] [Nonempty I]
```

## New

The same section command remains. The following private helpers each locally omit
those section instances; the scope ends at the corresponding theorem.

```lean
omit [IsDirected I (· ≤ ·)] [Nonempty I] in
private theorem homTransition_product {a b d : Object c} {k l : I}
    (ha : a.1 ≤ k) (hb : b.1 ≤ k) (hd : d.1 ≤ k) (h : k ≤ l)
    (f : (c.T ha).obj a.2 ⟶ (c.T hb).obj b.2)
    (g : (c.T hb).obj b.2 ⟶ (c.T hd).obj d.2) :
    homTransition c (k := ⟨k, ha, hd⟩) (l := ⟨l, ha.trans h, hd.trans h⟩) h (f ≫ g) =
      homTransition c (a := a) (b := b) (k := ⟨k, ha, hb⟩)
          (l := ⟨l, ha.trans h, hb.trans h⟩) h f ≫
        homTransition c (a := b) (b := d) (k := ⟨k, hb, hd⟩)
          (l := ⟨l, hb.trans h, hd.trans h⟩) h g := by
  simp [homTransition, Functor.map_comp, Category.assoc]
```

```lean
omit [IsDirected I (· ≤ ·)] [Nonempty I] in
private theorem compAt_transition {a b d : Object c}
    (f : HomRepresentative c a b) (g : HomRepresentative c b d)
    (m n : I) (hf : f.1.1 ≤ m) (hg : g.1.1 ≤ m) (h : m ≤ n) :
    compAt c f g m hf hg = compAt c f g n (hf.trans h) (hg.trans h) := by
  unfold compAt
  rw [← homClass_transition c
    (k := ⟨m, f.1.2.1.trans hf, g.1.2.2.trans hg⟩)
    (l := ⟨n, f.1.2.1.trans (hf.trans h), g.1.2.2.trans (hg.trans h)⟩) h]
  congr 1
  rw [homTransition_product c _ (f.1.2.2.trans hf), homTransition_comp,
    homTransition_comp]
```

```lean
omit [IsDirected I (· ≤ ·)] [Nonempty I] in
private theorem mapHomRepresentative_transition {a b : Object c}
    {k l : CommonStage a.1 b.1} (h : k ≤ l) (f : HomAt c a b k) :
    mapHomRepresentative c ⟨l, homTransition c h f⟩ =
      mapHomRepresentative c ⟨k, f⟩ := by
  have ha : (c.iso (k.2.1.trans h)).inv.app a.2 =
      (c.iso k.2.1).inv.app a.2 ≫ (c.iso h).inv.app ((c.T k.2.1).obj a.2) ≫
        (c.Φ l.1).map ((c.tau k.2.1 h).hom.app a.2) := by
    have he : (c.iso (k.2.1.trans h)).app a.2 =
        (c.Φ l.1).mapIso ((c.tau k.2.1 h).app a.2).symm ≪≫
          (c.iso h).app ((c.T k.2.1).obj a.2) ≪≫ (c.iso k.2.1).app a.2 :=
      Iso.ext (c.compatibility k.2.1 h a.2)
    simpa only [Iso.trans_inv, Functor.mapIso_inv, Iso.symm_inv, Iso.app_inv,
      Iso.app_hom, Category.assoc] using congrArg Iso.inv he
  dsimp only [mapHomRepresentative]
  rw [ha, c.compatibility k.2.2 h b.2]
  simp only [homTransition, Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app, Iso.hom_inv_id_app_assoc]
  dsimp only [Functor.comp_obj]
  simp only [Category.comp_id]
  have hn := (c.iso h).hom.naturality f
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc ((c.Φ l.1).map ((c.T h).map f)), hn]
  simp
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.FilteredTwoColimitModel | E1 | Assigned item; fills proofs and adds private helpers; all existing public signatures and definitions are unchanged. |
| Sheaf.CategoryTheory.FilteredTwoColimitCharacterization | unclaimed | Sole direct importer; all public declarations and definitions used by its unchanged statement remain identical. No adaptation. |

The private helpers cannot appear in public signatures or be referenced by
importers. The characterization statement, its source module, and the existing
public declaration headers were checked. Transitive users see the same interface.
No upstream module is modified.

## Status

landed 20261021T061004-L-1682422 2026-10-21 (merge of deliver/E1/Sheaf.CategoryTheory.FilteredTwoColimitModel)
