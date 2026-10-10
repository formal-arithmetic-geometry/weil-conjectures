# Stage 1 report

1. Files written:

- `dag/nodes/sec-picard-framework/lem-pc-hilb-containment-locus.json` (repaired statement and proof)
- `dag/nodes/sec-picard-framework/lem-pc-affine-containment-ideal.json` (repaired statement-only unsplit node; no Mathlib match)

2. Attachments: none.

3. WANTED: the local Stacks source file for Tag 0B97 is not in this checkout; the split follows the theorem and proof text recorded in the imported node and the project source comment.

4. The returned version incorrectly localized on affine opens of `X_T` and assumed a chosen basis and finitely many generators. I changed Step 1 to localize only on `T`, use `Z_U = Spec(B)` with `B` finite projective over `R`, and define the coefficient ideal basis-free using all `R`-linear functionals. Step 2 now uses the universal characterization to prove localization compatibility, rather than a nonexistent globally chosen finite free presentation. Step 3 cites the existing closed-immersion lift and factorization-by-ideal-inclusion leaves, and the item now introduces `T` and `X_T` explicitly.

## Not duplicates

`lem-pc-affine-containment-ideal` vs existing DAG nodes: searches for Tag 0B97, coefficient ideals, finite locally free containment, and the universal dual-functional criterion found no existing statement.

`lem-pc-affine-containment-ideal` vs `lem-pc-hilb-containment-locus`: the new node is the affine finite-projective algebra criterion; the item is the global closed subscheme representing containment for all base changes.

## Review by C1

I reread the returned item, Tag 0B97's recorded proof route, and the statements of `lem-weil-pbc-affine-ideals-closed-subscheme`, `lem-weil-pbc-closed-immersion-lift-ideal-kills-sections`, and `lem-weil-pbc-closed-immersion-factor-ideal-inclusion`. Step 1 now takes an affine `U=Spec(R)` in `T`, identifies `Z_U` with `Spec(B)` for finite locally free `B`, and applies exactly the repaired affine node to the ideal `J_U` cutting out `W` inside `Z_U`. Step 2 uses the existing gluing node's stated localization hypothesis; equality after localization is elementary from the coefficient ideal's universal property. Step 3 checks the affine pullback criterion on a cover of `T'`, then uses the lift node for the forward factorization and the factor-ideal node for the converse; its hypotheses match the ideal-sheaf vanishing and inclusion used. I verified the item statement now defines `T` over `S` and `X_T`, and that all cited node quotes in `citations.json` are verbatim. I also reran the required Mathlib searches for the item and affine node: LeanFinder, Loogle, grep, and LeanSearch (LeanSearch unavailable); no direct Mathlib theorem states either result.

## Second reading by C1

- Item statement: checked against Picard Schemes `pic.tex`, Lemma `lemma-hilb-d-of-closed`, Tag `0B97`, including the hypotheses on `S`, `T`, `X_T`, the two closed immersions, finite locally free degree, the universal base-change iff, and the zero/field/empty-scheme cases; verdict: agrees.
- Step 1: checked against the direct affine paragraph of Tag `0B97` and the exact statement of `lem-pc-affine-containment-ideal`; the pullback of a closed immersion to `Spec(B)` is `Spec(B/J_U)`, and finite locally free over an affine base gives finite projective `B`; verdict: sound, with the affine pullback observation elementary.
- Step 2: checked against the localization compatibility required by `lem-weil-pbc-affine-ideals-closed-subscheme`; equality follows by testing both universal vanishing properties on quotient maps, so the elementary marking is justified; verdict: sound.
- Step 3: checked against the factorization paragraph of Tag `0B97` and the verbatim statements of the affine criterion, closed-immersion lifting criterion, and ideal-inclusion criterion; the revised text explicitly passes from the affine cover of `T'` to an affine cover of `Z_{T'}` before applying the lifting criterion; verdict: sound in both directions and under arbitrary base change.
- `lem-pc-affine-containment-ideal`: statement tested for `R=0`, a field, `B=R`, `J=0`, and `d=0`; finite-projective dual functionals give exactly the claimed base-change vanishing criterion. Blueprint search and repository grep found no duplicate; Mathlib searches are recorded and found no exact theorem; verdict: valid unsplit node.
- Changes: clarified Step 3's sheaf-local vanishing argument so the cited lifting node's hypotheses are visibly met; retained the existing closed-immersion definition dependency, which covers both `W` and `Z`; no statement or citation quote required alteration.
