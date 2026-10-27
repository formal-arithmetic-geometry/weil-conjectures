# Q78: lem-sfb-regular-surface-vector-bundle-extension

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-regular-surface-vector-bundle-extension.json`: item, split into four steps; mathematical statement unchanged.
- `dag/nodes/sec-six-functors-basics/lem-sfb-regular-surface-reflexive-locally-free.json`: new statement-only lemma, Stacks 0B3N; unsplit, no Mathlib match.
- `citations.json`: eleven entries, one for every step/node citation, quoting the cited statement verbatim.
- `searches.jsonl`: actual msearch.py log. Six relevant logged searches are recorded on the new lemma; the item retains its inherited searches and adds the Q78 extension searches.
- `report.md`: this report. No repository, launcher, Lean, chapter or unit file was written.

There was no prior sandbox node, report, split or search log. I started from the current read-only repository item.

## Attachments

None. Searches of `lean/WeilConjectures/` by the item id, reflexivity, Hartogs, codimension two and vector-bundle/local-freeness concepts found no project declaration proving every clause. The codimension-two finite-etale extension file mentions locally free modules but does not state this arbitrary-bundle equivalence. Ordinary duality declarations do not imply this theorem. I also checked the relevant `lean/Sheaf/` keyword hits as reference material.

## Sources and blueprint route

The proof uses local Stacks sources, not the unavailable Alper--Halpern-Leistner--Heinloth PDF cited upstream of the item. No document is wanted for this split.

I read `divisors.tex`, the statement and proof of `lemma-reflexive-S2-extend` (0EBJ), and the statement and proof of `lemma-reflexive-over-regular-dim-2` (0B3N). I also read `coherent.tex`, `lemma-coherent-Noetherian` (01XZ), including its explicit finite-locally-free coherence consequence, and `properties.tex`, `lemma-regular-normal` (0569). The existing normal reflexive equivalence is exactly the needed normal specialization of 0EBJ: its statement, unlike a mere definition of reflexivity, supplies coherence of the actual direct image, both unit and counit, and Hom bijectivity.

I read the chapter and unit records and the latest blueprint chapter, unit, direct-image statement and direct-image proof in `literature/blueprint/latest/`. This is a supporting input in the inherited direct-image alteration chain; it implements step 2 of the existing reductive nodal equivariant torsor extension, without replacing a unit or chapter argument. `blueprint_refs.py ancestor` reports `None` for the current item's creation chain. I kept that actual inherited `from.node = null`, carried its precise place into the new lemma, and prepended this item to the new lemma's `via`. Searches of the whole blueprint by `reflexive`, `regular scheme`, `locally free`, and 0B3N, plus a text search of the latest blueprint, found no blueprint node stating the new dimension-two criterion or the whole item. The smooth-base-change reflexive-algebra mention concerns a finite-etale extension, not this arbitrary coherent-sheaf criterion.

## What was wrong or missing

The item was statement-only. Its two cited Stacks results are valid, and no statement dispute or correction was necessary. Its definition dependencies did not distinguish the topological dimension of the scheme from the Krull dimension of its local rings, so I added the topological-dimension definition alongside the existing ring-dimension definition. I also added the existing definitions underlying Noetherianity, the open immersion and module pullback/direct-image adjunction. The mathematical statement is unchanged.

The existing normal reflexive open-equivalence lemma saves a duplicate new 0EBJ node. A separate 0B3N criterion remains necessary: the earlier torsion-free-on-regular-curves lemma only covers dimension at most one and uses a weaker module property. New nodes for local coherence of bundles, restriction preserving local trivializations, the dimension of an open subscheme, or the final categorical assembly would be elementary and have not been created.

## Not duplicates

lem-sfb-regular-surface-reflexive-locally-free vs lem-sfb-regular-surface-vector-bundle-extension: the new lemma identifies two properties of one coherent module on a regular scheme of dimension at most two; it has no open complement, no direct image, no equivalence of restriction categories and no morphism-extension assertion. The item must additionally prove its actual direct image is coherent reflexive using the existing 0EBJ node and assemble the full equivalence.

lem-sfb-regular-surface-reflexive-locally-free vs lem-sfb-reductive-nodal-equivariant-torsor-extension: the existing parent concerns equivariant reductive-group torsors over a particular nodal surface and needs the present item's vector-bundle extension as an input. The new criterion concerns arbitrary coherent modules on any regular scheme of dimension at most two and contains no torsor or equivariance assertion.

lem-sfb-regular-surface-reflexive-locally-free vs lem-sfb-normal-reflexive-open-equivalence: the existing node concerns extension of coherent reflexive sheaves across a normal codimension-two complement in unrestricted dimension; it does not identify them with locally free sheaves on a regular surface.

lem-sfb-regular-surface-reflexive-locally-free vs lem-sc-regular-curve-torsionfree-free: the existing node assumes integrality and dimension at most one, tests torsion-freeness, and also gives constant rank; the new node handles dimension two, requires reflexivity, and makes no integrality or constant-rank assertion.

The same-tag DAG search found only the item and its torsor parent for 0B3N. I read both before introducing the new criterion.

## Mathlib searches read

All new recorded queries were executed through the mandated msearch.py command under Q78 and this item. No search was inferred or invented. The two leanfinder phrasings ask respectively about coherent reflexive sheaves on regular schemes of dimension at most two and about regular Noetherian schemes in dimensions zero, one and two. The first returned finite-type/finite-presentation infrastructure; the second returned basic module-sheaf category operations, rank-local-constancy results, and `Module.instIsReflexiveOfFiniteOfProjective`. Neither provides the difficult implication reflexive implies locally free. Loogle's combined `"IsReflexive", "IsRegular"` query had no hits. LeanSearch's criterion query returned `Module.IsReflexive.of_finite_of_free` and finite-presentation infrastructure. A grep of AlgebraicGeometry for reflexive/reflexivity/Hartogs had no hits. The targeted Dual grep located `Module.IsReflexive.of_finite_of_free` at `Mathlib/LinearAlgebra/Dual/Lemmas.lean:259`; I read lines 251-262 and verified this only proves the opposite implication for modules. Thus the criterion is not a Mathlib leaf.

For the item, LeanSearch returned `Scheme.Modules.restrictFunctorAdjCounitIso`. I read `Mathlib/AlgebraicGeometry/Modules/Sheaf.lean:416` and its adjacent adjunction/counit declarations: they prove the counit for an arbitrary open immersion, not coherence or local freeness of pushforward or the unit for bundles. The other semantic and grep hits concern free sheaf generators, ordinary module reflexivity, categorical reflexive coequalizers, or topological codimension. None states the entire item. All services used here answered; none is mislabeled unavailable or no-match after failure.

## Review by Q78

I checked the split against delivery-errors B through E with the statements and the four Stacks places open. For the only new node, 0B3N really assumes a regular scheme of dimension at most two and a coherent module and concludes the equivalence between reflexivity and finite local freeness. The node introduces its own scheme, sheaf, dual and evaluation; its notions cite their actual definitions; its proof and proof dependencies are empty. It does not outsource a clause of the item's extension theorem. Its source names the stable tag and exact TeX label. The recorded searches are backed by the command log and their hits were read. No new Mathlib leaf or unverified declaration attachment is claimed.

Step 1 uses precisely the open-immersion, regular-scheme, dimension and finite-locally-free definitions. The stalks on an open subscheme are the original local rings, so the regular local condition and local Noetherianity are preserved. The proof of the dimension inequality is written out by closures and intersection with the open; it does not silently assume separatedness. Restricting the trivializations directly proves restriction preserves bundles. These are elementary observations, not new nodes.

Step 2 cites the finite-locally-free definition, `pqf-lem-coherent-ft-locnoeth`, and the new criterion. The coherence node's actual statement says coherent if and only if quasi-coherent of finite type; it does not itself assert that a bundle is coherent, so I supplied the affine-trivialization and finite-standard-generator argument establishing those two inputs. Both X and U are locally Noetherian by step 1. The new criterion applies to both, and says exactly that a coherent module is reflexive if and only if it is finite locally free. Keeping all module morphisms identifies full subcategories, not just isomorphism classes of objects.

Step 3 cites clause (1) of `rem-pc-regular-normal`, whose actual statement says regular implies normal, not merely a definition of normality. This verifies the extra hypothesis of `lem-sfb-normal-reflexive-open-equivalence`; integrality, local Noetherianity and the local-dimension bound at every omitted point are already the item's hypotheses. I read the latter node's statement in full: it explicitly gives the coherent reflexive direct image, unit, counit and Hom bijection used here. Applying the new criterion on X then proves local freeness of this very direct image. In particular the proof does not substitute a chosen coherent hull for j_*V or use an unstated result inside a cited node's proof.

Step 4 uses the units and counits supplied by that same equivalence. I wrote the extension as eta_F inverse composed with j_*a composed with eta_E. Restriction gives the original map by the unit/counit identities, and naturality forces every extension to have that formula. Thus the last clause is for arbitrary module morphisms, with no invertibility assumption, and the required compatibility is explicit. Every use has a verbatim statement quote in citations.json. Both off-unit tools, regular implies normal and coherence iff quasi-coherent of finite type, are declared in split_report.tool_uses with their narrow purposes; I have not set the maintainer-owned tool_uses field.

Small cases: if dim X is zero or one, the complement condition leaves no omitted points and the conclusion reduces to the identity equivalence. In dimension two the complement may contain closed points, exactly where 0B3N is needed. Rank zero is allowed: duals and the direct image of the zero sheaf are zero, so no nonzero-rank hypothesis is used. The new criterion also permits the empty regular scheme, where both properties hold vacuously. The item itself excludes empty X by integrality; its generic point must be in U because its local dimension is zero. Over k[x,y], the ideal (x,y) has bidual the structure module and is not locally free at the origin, so replacing reflexivity by torsion-freeness would be false; this split makes no such replacement. No completeness, excellence, field, characteristic, separatedness or fixed-rank assumption was introduced.

I checked for duplicate lemmas, including the existing normal equivalence, affine reflexivity comparison, dimension-one torsion-free criterion and affine depth-two model; none supplies the missing 0B3N implication. No definition was cited as a hidden theorem beyond an explicitly stated equivalent characterization. No source argument was moved into an opaque long proof step: the four step lengths are 464, 561, 716 and 428 characters, all below 2000. The new statement's dependencies are definitions and cannot create a return edge to the item. Final acyclicity and preflight are checked by the required server dry run.

## Unfinished work

The new criterion is intentionally statement-only for its own later stage-1 item, as required for a one-level split. No part of the current item's assembly proof is left unstated. Validation and delivery results will be recorded below.

## Validation

The required `deliver.py Q78 lem-sfb-regular-surface-vector-bundle-extension --no-push` exited successfully: `OK (not pushed)` at dry-run commit `a4a4158f0b5`, server preflight passed. All cited ids exist and the eleven verbatim quotes were also checked against the current local node statements. The final push runs the required preflight again on its actual delivery commit.
