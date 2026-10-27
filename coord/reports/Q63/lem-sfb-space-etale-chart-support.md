# Worker report: lem-sfb-space-etale-chart-support

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-space-etale-chart-support.json`: statement unchanged, status split, four proof steps, refreshed Mathlib searches and split report.
- `dag/nodes/sec-six-functors-basics/lem-sfb-space-quasicoherent-geometric-stalk-tensor.json`: one new statement-only lemma, status unsplit, no Mathlib match. It states the module isomorphism of Stacks 05VP, rather than support or zero detection.
- `citations.json`: eight exact statement excerpts, one for every proof-step citation.
- `searches.jsonl`: actual outputs logged by msearch.py, used for the recorded queries. `prepare.py` is sandbox-only preparation, not part of the delivery.

## Attachments

None. Searched the live `lean/WeilConjectures/` for the blueprint id, algebraic spaces, quasi-coherent geometric stalks, and stalk/tensor/support terminology. There is no declaration giving this algebraic-space assertion with all its clauses. Ordinary scheme stalk and tensor statements do not provide an attachment. Nothing was compiled or written in Lean.

## WANTED

None. All mathematical sources used are in literature/stacks-project/.

## Findings and changes

The imported item was statement-only and mathematically correct. Its six statement dependencies were opened and retained: they actually introduce schemes, algebraic spaces and their etale ringed sites, quasi-coherent modules, the Zariski/etale comparison, ordinary module stalks and the point map. I read the chapter and unit records, the current latest blueprint chapter/unit and direct-image proof, and the historical provenance recorded on the item. The helper serves 07TY inside 07TZ, the coherent-support prerequisite in the existing alteration/dimension-one chain. The latest proof's direct-image paragraph does not itself mention this commutative-algebra sublemma. No chapter/unit route is changed. `blueprint_refs.py ancestor lem-sfb-space-etale-chart-support` reports `blueprint.from.node = None`; this inherited provenance is retained, with the item's existing concrete place and a more specific place on the new node.

The proof follows spaces-morphisms.tex, Tag 07TY, label lemma-support-covering, sentence by sentence. Its two substantive geometric inputs are 05VP and 04KF. The DAG already has 04KF in lem-sfb-space-strict-local-flatness, and 07QM(1) in lem-sc-strict-henselization-faithfully-flat. Only 05VP was missing. Faithful-flat zero detection is three lines from the definition and remains a proof step. The same holds for swapping tensor factors: its bilinear universal-property maps are inverse on pure tensors. I did not add nodes for either.

I expanded the item's asserted independence from the chosen geometric point. For a fixed point x, choose one atlas point v above it. The existing specified-lift lemma lifts each chosen geometric representative of x to that same v; applying the established comparison says its stalk vanishes exactly when the one fixed ordinary module stalk vanishes. This also proves independence away from the image of the particular map e. Merely choosing a geometric point above u would not by itself justify that global clause.

The new node has no proof, proof dependencies, or argument hidden in its statement. Its formula is an isomorphism of modules over the etale local ring, not a claim about residue fibres. Its coefficient ring is the structure sheaf, not the constant-coefficient etale sheaves used elsewhere in the project. It is a genuinely smaller tool: it computes the whole module stalk, while the item's proof still derives zero detection and equality of support subsets.

## Searches and reuse

Before writing the new node I searched all of dag/nodes/ for 05VP, lemma-stalk-quasi-coherent, strict henselization, quasi-coherent geometric stalks, tensor/stalk comparisons, and support. I read the relevant candidates, including lem-sfb-space-stalk-ideal-pullback: that statement only handles ideal stalks across square-zero thickenings, so it cannot supply the module comparison here. I also read the existing chart-ring lemma, the strict-henselization faithful-flatness lemma, the specified geometric lift, and the scheme Zariski/etale equivalence, and reuse them at exactly the stated level.

Whole-blueprint searches with tools/blueprint_refs.py included 05VP, stalk-quasi-coherent, 07TY, support, and geometric stalk. The tag-specific searches found no blueprint node giving the missing comparison. No same_as match was found. The new node inherits the item chapter and unit, and extends its via chain by the item itself.

For the new node I ran msearch.py with two different LeanFinder phrasings (geometric chart stalk tensor formula; change from Zariski to etale topology), Loogle with `"stalk", "tensor"`, LeanSearch with the strict-henselization formulation, and source grep for stalk/tensor/AlgebraicSpace. I read all returned hits. ModuleCat.Tilde.stalkIso and its companion hits concern ordinary affine Zariski stalk localization; the semantic service returned no etale algebraic-space module stalk formula. The pinned local Tilde.lean was also opened. The other Loogle hits are RingHom.SurjectiveOnStalks and ranks over prime spectra. SheafOfModules.IsQuasicoherent is only a definition. None specializes in one line to 05VP. No search service was unavailable.

For the parent I retained the pre-existing searches and added actual Q63 searches of support/ordinary-stalk/geometric-stalk terminology with LeanFinder, Loogle, LeanSearch and grep. The apparent support_comap hit was opened in Mathlib/AlgebraicGeometry/IdealSheaf/Functorial.lean: it is the closed set defined by an ideal, not the nonzero-stalk support of an arbitrary module on a space. The ring support/rank hits likewise do not compute algebraic-space sheaf stalks. All newly recorded query strings match searches.jsonl exactly.

## Not duplicates

The DAG and blueprint have no existing node with source 05VP, so there is no same-tag pair requiring a difference entry. The 04KF and 07QM results are reused, not recreated. In particular:

- lem-sfb-space-quasicoherent-geometric-stalk-tensor vs lem-sfb-space-stalk-ideal-pullback: the former compares an arbitrary quasi-coherent module's ordinary chart stalk to its geometric stalk; the latter computes geometric ideal pullback stalks in a square-zero closed-immersion square and never compares ordinary chart stalks.
- lem-sfb-space-quasicoherent-geometric-stalk-tensor vs lem-sfb-space-strict-local-flatness: the former computes module stalks; the latter identifies structure-ring stalks with strict henselizations and tests flat morphisms, with no assertion for a module M.
- lem-sfb-space-quasicoherent-geometric-stalk-tensor vs lem-trf-scheme-zariski-etale-quasi-coherent-equivalence: the latter compares categories and section functors on schemes; it does not identify geometric stalks over an algebraic space with tensor extensions of ordinary local stalks.

## Tool uses

The sole off-unit proof citation is lem-sc-strict-henselization-faithfully-flat (unit sk-thm-br), used as the generic commutative-algebra tool in the published 07TY proof. It does not replace any unit route. The two same-unit geometric tools are also explained in split_report.tool_uses. The scheme Zariski/etale comparison remains a statement dependency describing the meaning of M_U; it is not an alternative proof route.

## Unfinished work

The new 05VP statement is intentionally unsplit, as required for a one-level split. Its later worker should follow the colimit argument in the 05VP proof: chartwise quasi-coherence makes transition stalks tensor base changes, and tensor commutes with the pointed-neighbourhood colimit. This argument is not smuggled into the new statement. There is no unresolved mathematical issue in the parent's assembly proof.

## Review by Q63

I read the actual source text for the item, spaces-morphisms.tex Tag 07TY (lemma-support-covering), and for the one new node, spaces-properties.tex Tag 05VP (lemma-stalk-quasi-coherent), including its proof. Both permit an arbitrary etale map from a scheme and an arbitrary quasi-coherent module. Neither requires finite generation, Noetherianity, quasi-compactness, or a surjective chart. I also read 04KF (lemma-describe-etale-local-ring), 07QM(1) (lemma-dumb-properties-henselization), and the geometric-support definition 04KA (definition-support). The ring map in step 1 is the natural local-ring map for the given pointed chart, with its actual residue embedding; replacing it by an arbitrary isomorphic ring without the A-algebra structure would be insufficient. The cited chart-ring statement explicitly gives the correct strict henselization and embedding, and the faithful-flatness statement therefore applies to the ordinary local ring A with that choice of separable residue closure.

For step 1 I opened all three cited statements: the new 05VP node gives exactly N tensor_A B isomorphic to the geometric stalk; lem-sfb-space-strict-local-flatness supplies precisely B = A^sh as the chart local algebra; lem-sc-strict-henselization-faithfully-flat supplies faithful flatness of that map. None of these is taken from the proof of a node. Step 2 cites the exact-complex definition of faithful flatness, not just the definition of flatness. The test complex 0 -> N -> 0 has zero composite and is exact exactly when N = 0, so reflecting its exactness supplies the direction that ordinary flatness would not give. The tensor definition supplies the inverse switch maps, checked on generators. This is the elementary part of the argument and uses no finite-module version of Nakayama.

For step 3 I opened def-trf-algebraic-space, which asserts the existence of a surjective etale scheme atlas, and lem-sfb-etale-geometric-point-specified-lift, whose statement permits every specified chart point over x and preserves the already chosen algebraically closed field. That is precisely what is needed to compare every geometric representative with one ordinary stalk. The universal comparison in steps 1 and 2 applies to the atlas just as to e. In step 4 I opened def-a1-space-point-topology: the point map is defined by residue-field representatives, so e composed with a geometric point over u represents |e|(u). Taking the negation of the vanishing equivalence and checking membership pointwise is elementary. Every citation has a verbatim statement substring in citations.json, checked while writing the files.

I checked B1--B9 on the new node: it introduces S, X, M, e, U, the geometric points, both coefficient rings and both stalks; gives the tensor formula in TeX; cites the actual definition nodes and 05VP label; keeps proof empty; records actual searches without claiming a Mathlib match; and fills provenance. C1/C4 are addressed by the three exact step-1 statements and the direct definition argument in step 2. The support equality is proved in the parent, so D1/D2 do not arise. All proof steps are below 2000 characters and the total is under 3000. No SGA source is used.

For small cases I checked the empty chart (the equality is vacuous), the zero module (both supports empty), identity and open-immersion charts, and a field with different algebraically closed extensions (each geometric stalk vanishes exactly when the same ordinary stalk does). Infinite direct sums of structure modules cause no change: the faithful-flat definition reflects exactness for all modules, not only finite ones. Nonreduced and non-Noetherian local rings are also allowed by 07QM, and quasi-coherence is explicitly present where the tensor formula uses it. A non-surjective chart only tests its own image; the independence proof separately uses a surjective atlas. During this reading I corrected the support-definition tag in the new proof source from 04KB to the verified 04KA. No statement change was necessary.
