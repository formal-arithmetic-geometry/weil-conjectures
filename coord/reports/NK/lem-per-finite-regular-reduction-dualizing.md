# Stage-1 report: lem-per-finite-regular-reduction-dualizing

## Files written

All node paths below are under `dag/nodes/sec-deligne-laumon-a1/` in this sandbox.

- `lem-per-finite-regular-reduction-dualizing.json`: existing statement, split into seven steps; no statement change.
- `def-per-potential-dualizing-complex.json`: definition, prime-power-coefficient pinned potential complexes; no Mathlib match.
- `lem-per-potential-dualizing-regular-unit.json`: statement, canonical regular-unit pinnings with twist and shift; no Mathlib match.
- `lem-per-potential-dualizing-finite-pullback.json`: statement, finite-type exceptional normalization and transitivity; no Mathlib match.
- `lem-per-potential-dualizing-uniqueness.json`: statement, existence, uniqueness with fixed pinnings and bounded constructible finite-Tor property; no Mathlib match.
- `lem-per-potential-dualizing-coefficient-tower.json`: statement, normalized derived reductions and exceptional coefficient comparison; no Mathlib match.

The five new nodes are statement-only/definition-only unsplit interfaces. There are no Mathlib leaves. `citations.json` contains a verbatim statement quotation for every step/node pair. Actual msearch responses are retained in `*.hits.txt` and the command's `searches.jsonl`; no service failure was relabelled as absence.

## Attachments

None. Read-only searches in `weil-src-slopmaster2/WeilConjectures/` found no declaration with the item tag, no potential-dualizing implementation, and no declaration proving the full arbitrary-field regular-reduction assertion. Smooth-purity declarations in `EtaleCohomology/Purity/Smooth/Basic.lean` concern the smooth setting and cannot establish the imperfect-field claim here. Upstream master is reference material only. No Lean was written or compiled.

## WANTED

None. Both ILO and Bhatt–Scholze are available locally and were read. No prohibited source is used.

## Corrections and unfinished work

The imported statement is retained, including nonempty irreducible underlying space, regularity only of its reduction, arbitrary field, all prime-power coefficients, power-map transitions, and the relative dimension function. The empty imported proof is replaced by the argument. The fixed unit is the perverse-curve unit; this auxiliary local model realizes its dimension-normalized Verdier-duality route and changes neither its statement nor its steps. No unit record is written because this item is not its key node.

The only incomplete mathematical work is the future splitting of the five new interfaces. Their sources and statements specify it. In particular uniqueness is for *pinned* complexes, not uniqueness of all dualizing objects; ordinary dualizing objects can differ by invertible complexes. The coefficient comparison is derived tensor reduction, not the RHom coefficient operation of ILO XVII 6.2.1.1. The latter alone would not prove the tower clause. Bhatt–Scholze 6.7.18 and 6.7.20 supply the relevant operation.

## Searches and reuse

The whole DAG was searched for potential dualizing complexes, normalization, regular dualizing complexes, nilpotent thickenings, excellence, dimension formulas, and roots of unity. `tools/blueprint_refs.py` searches included `dualizing`, `potential`, `regular reduction`, `nilpotent`, `normalized`, `pinning`, `regular unit`, `coefficient tower`, `potential dualizing`, `exceptional inverse image`, and `negative codimension`; `ancestor` returns `lem-per-artin-gabber-affine-curve`. No blueprint node states any new interface with prime-power coefficients. The searches located the existing geometry and etale-twist nodes actually cited in the proof. Existing finite-residue potential nodes, which appeared in the shared tree during this session, were reopened and read rather than ignored.

For each proposed new id, msearch ran LeanFinder with its own statement, LeanSearch with another phrasing, Loogle for `"dualizing"`, and grep for potential/dualizing/pinning terminology in Mathlib's AlgebraicGeometry. LeanFinder returned scheme sections, local cohomology of modules, generic derived-category boundedness, or perfectoid rings; LeanSearch returned etale ring maps, ordinary residue fields, category-theoretic pullback compositors, or linear-algebra orientations. None concerns residue-compatible etale local cohomology pinnings. Loogle and the Mathlib grep had no hits. The item was also searched with its own phrasing and second semantic phrasing. This is not an inference from missing theorem names alone.

## Not duplicates

- def-per-potential-dualizing-complex vs def-per-potential-dualizing: the existing definition fixes Lambda=F_ell; the new definition permits Z/ell^n for every n. This distinction matters for n>1, and F_ell has no unital algebra map to Z/ell^n for n>1. The new node gives the actual residue-transition construction and pinning equation for that coefficient ring.
- lem-per-potential-dualizing-finite-pullback vs lem-per-potential-extraordinary-pullback: the existing extraordinary-pullback statement is restricted to F_ell. The new one is the same literature theorem at the prime-power stages required here, which is not a specialization of the existing statement.
- lem-per-potential-dualizing-uniqueness vs lem-per-potential-local-duality: local-duality states evaluation biduality over finite fields; it does not give uniqueness with fixed pinnings, and it does not allow the non-field rings Z/ell^n. The new node is ILO's normalization/uniqueness and constructibility result, not another biduality statement.
- lem-per-potential-dualizing-coefficient-tower vs lem-per-adic-exceptional-projection: the existing adic theorem gives reductions of integral extraordinary pullback, but does not state pinning compatibility or the normalized potential systems on arbitrary excellent schemes. The new node supplies exactly that missing finite-level normalization information.
- lem-per-potential-dualizing-regular-unit vs lem-per-finite-regular-reduction-dualizing: the new regular-unit theorem is about the canonical constant sheaf with local support pinnings for negative local codimension on any excellent regular scheme. It says nothing about a structure morphism to a field, nilpotent thickenings, or the identification of an exceptional adjoint. The item's argument still has to calculate the relative dimension function, compare the two pinned objects, and descend through reduction. It is not the item or a renamed clause.

## Review by NK

I read ILO Expose XVII Definitions 1.1.1, 1.2.3.1, 1.3.1, 1.4.1 and 2.1.1–2.1.2 for the definition, including the tame residue model and inseparable-degree normalization. For the regular-unit node I read Proposition 2.4.4.1 and its reference to 2.4.1.1: the unit is normalized for negative codimension, not for transcendence degree until the twist/shift is inserted. Proposition 4.1.2 and Remark 4.1.3 are the source of the new pullback node, with their Noetherian, excellent, compactifiable finite-type hypotheses retained. Theorem 5.1.1 and Propositions 6.2.2.1–6.2.2.3 give uniqueness, constructibility and finite Tor dimension. The proof of 6.2.2.1, printed page 294, explicitly reduces to the reduced regular connected case and identifies the potential object as Lambda(delta(eta))[2delta(eta)]. For the tower node I read Bhatt–Scholze Lemmas 6.7.18 and 6.7.20, including the two scalar-change squares and their normalized-potential construction. I did not replace tensor reduction by ILO's RHom coefficient construction.

In step 1 I opened the reduction definition, field excellence, finite-type/localization excellence, Nagata compactification, closed-immersion properness, finite-type dimension finiteness, and locally-finite-presentation statements. They provide respectively the actual closed subscheme, excellent affine rings, compactifiability, properness of i, finite d, and the finite-presentation hypothesis needed later. No geometric regularity or separability of the base extension is inferred. The finite affine-cover and irreducible-implies-connected deductions are elementary here.

For step 2 I opened `lem-asd-etale-finite-twist-pullback`: it explicitly gives local rank-one freeness on small etale sites, roots pullback, and the exponent-change power map. This avoids using a pro-etale theorem as though its statement were etale. N=ell^n is invertible and kills A=Z/ell^n, exactly its hypotheses. For step 3 I opened `lem-sc-dimension-locally-algebraic` and `lem-kun-dimension-formula`. The first gives dim_t(T)=dim(T) for this irreducible locally finite-type scheme; the second then gives d=c(t)+trdeg. Regularity alone would not have justified constant local topological dimension on an arbitrary scheme.

Step 4 uses only the regular-unit and finite-pullback statements: the coefficient unit at the field has codimension zero, the two structure morphisms have the compactifications checked in step 1, and regularity is applied only to T. Their composition clause identifies the pinnings of i!a! and b!. Step 5 uses the uniqueness node for two pinned complexes with exactly the same dimension function, and its separate bounded-constructibility assertion; no unnormalized uniqueness is invoked.

For step 6 I opened topological invariance, the compact-support definition and its comparison theorem. The first really states an equivalence compatible with inverse/direct image. Applied to the reduction (a universal homeomorphism by the affine nil-ideal calculation written in the step), it gives exact inverse equivalences. Because i is proper, its identity-open compactification computes Ri! as Ri*. Thus its right adjoint is the inverse equivalence. This explicitly accounts for the identification i!=i^{-1}; the definition of reduction alone would not establish it. Full faithfulness lifts the isomorphism, with twist pullback already checked in step 2. All complexes remain on constant-coefficient etale module categories.

For step 7 I checked that the coefficient-tower node says both that tensor reduction preserves the normalized pinnings and that the actual exceptional comparison agrees with them. The regular-unit statement supplies reduced regular pinnings. The uniqueness statement then compares the two morphisms in the coefficient square, and faithful reduction pullback detects its commutation on X. The final calculation is written in generators: zeta goes to zeta^ell, corresponding to scalar quotient; its tensor powers give the dth twist. Local freeness makes derived reduction ordinary. This addresses both the transition map and the isomorphism, rather than an existence-only assertion at separate levels.

Small cases checked: d=0, including a finite purely inseparable extension of an imperfect field, has the untwisted unit and no added separability assumption; a nonreduced Artinian thickening is handled by etale invariance; A^1 has Lambda(1)[2], confirming both signs; n=1 recovers the existing residue-coefficient construction, whereas n>1 genuinely needs the new coefficients; d=0 uses the coefficient quotient itself, not a roots-of-unity convention for a nonexistent positive twist. Negative m in the regular-unit interface uses dual powers, with supported degree shifted by 2m. Empty X remains excluded exactly as in the item; none of the proof forces a choice of a generic point of the empty scheme.

I checked B–E against the files: new nodes have no hidden proofs, all their objects and coefficients are introduced, blueprint ancestry has the two intervening created nodes after this item, searches were actually run, no smooth-purity trace route is introduced, and every non-elementary step names the statement supplying it. All steps are below 2000 characters, so no long inline comparison remains hidden. I corrected the first draft to record finite presentation explicitly and to use complete verbatim statement quotations in citations.json. Off-unit results are declared as generic tool uses in split_report; the unit route is unchanged. The server dry run is the remaining mechanical verification and will be recorded below.

## Validation

The required server `review_split` check passed. The required delivery dry run exited successfully with `OK (not pushed)` at candidate 61663025af; its full server preflight passed. The final dry run is repeated after adding this validation record, before the direct push required by the brief. No local check_dag/review_split/preflight program, compiler, Lake, live-project write, launcher edit, or separate agent was used.
