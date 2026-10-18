# CompactSupportFormalism private proof helpers

## Reason

Stage-3 preflight flags the added section-local `variable` and `include` commands as a
possible change to what importers see and requires this record. The four added lemmas are
private, fully proved helpers. `BaseChangeCube` and `TriangleBaseChange` are closed sections;
their variable contexts do not escape. No existing declaration's signature, definition,
visibility, universe, or instance is changed. No public definition refers to a private helper.
The three public theorem bodies may refer to these private proofs.

## Old

There are no corresponding helper declarations in the original module. All existing public
signatures and definitions remain verbatim; the original three theorem holes are replaced
by proofs.

## New

The following signatures occur verbatim in the delivered module, in the explicitly declared
scheme, morphism, pullback-square and formalism contexts of their closed sections:

```lean
private lemma baseChange_cube_hom_app (N : F.obj B) :
    (F.sh k').map ((F.sqIso a r' r b wr).hom.app N) ≫
      (F.baseChange r' k' i' p' Q'.w).natTrans.app ((F.pb b).obj N) ≫
      (F.pb p').map ((F.baseChange b i' i d I.w).natTrans.app N) ≫
      (F.sqIso c p' p d wp).inv.app ((F.sh i).obj N) =
    (F.baseChange a k' k c K.w).natTrans.app ((F.pb r).obj N) ≫
      (F.pb c).map ((F.baseChange r k i p Q.w).natTrans.app N)
```

```lean
private lemma exchange_cube_app [F.HasBaseChange] (M : F.obj A) :
    haveI := HasBaseChange.isIso_baseChange (F := F) Q
    haveI := HasBaseChange.isIso_baseChange (F := F) Q'
    haveI := HasBaseChange.isIso_baseChange (F := F) K
    haveI := HasBaseChange.isIso_baseChange (F := F) I
    (F.pb d).map ((F.exchange r k i p Q.w).natTrans.app M) ≫
      (F.pfBaseChange c p' p d wp).natTrans.app ((F.sh k).obj M) ≫
      (F.pf p').map (inv ((F.baseChange a k' k c K.w).natTrans.app M)) =
    inv ((F.baseChange b i' i d I.w).natTrans.app ((F.pf r).obj M)) ≫
      (F.sh i').map ((F.pfBaseChange a r' r b wr).natTrans.app M) ≫
      (F.exchange r' k' i' p' Q'.w).natTrans.app ((F.pb a).obj M)
```

```lean
private lemma baseChange_open_comp_inv_app [F.HasBaseChange] (N : F.obj X) :
    haveI := HasBaseChange.isIso_baseChange (F := F) hfi
    haveI := HasBaseChange.isIso_baseChange (F := F) hci
    haveI := HasBaseChange.isIso_baseChange (F := F) hq
    inv ((F.baseChange ha T'.q T.q hc hq.w).natTrans.app ((F.sh T.cf.i).obj N)) ≫
      (F.sh T'.q).map (inv ((F.baseChange gX T'.cf.i T.cf.i ha hfi.w).natTrans.app N)) ≫
      (F.shComp' T'.cf.i T'.q T'.cfg.i T'.i_q).inv.app ((F.pb gX).obj N) =
    (F.pb hc).map ((F.shComp' T.cf.i T.q T.cfg.i T.i_q).inv.app N) ≫
      inv ((F.baseChange gX T'.cfg.i T.cfg.i hc hci.w).natTrans.app N)
```

```lean
private lemma shriekBaseChange_compIso [F.HasProperExchange] :
    Functor.whiskerRight (F.compIso T).hom (F.pb gS) ≫
      (F.shriekBaseChange T.cfg T'.cfg hc hci hcp).natTrans =
    (F.shriekBaseChange T.cf T'.cf ha hfi hfp ≫ₕ
      F.shriekBaseChange T.cg T'.cg hb hgi hgp).natTrans ≫
      Functor.whiskerLeft (F.pb gX) (F.compIso T').hom
```

The new section contexts are used only by these private lemmas. The `include hq hp` command
ensures that the triangle helper retains its two compatibility hypotheses, which occur only
in its proof, rather than dropping them during section-variable generalization.

## Users

A read-only `tools/downstream.py --uses` check for all four helper names finds no existing
consumer. Their visibility also prevents external use. No downstream module needs adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| WeilConjectures.SixFunctors.LowerShriek.Formalism.BaseChange | F4 | Adds private proof helpers and proves the three existing theorems; existing public interface unchanged. |

## Status

landed 20261018T062750-L-649152 2026-10-18 (merge of deliver/F4/WeilConjectures.SixFunctors.LowerShriek.Formalism.BaseChange)
