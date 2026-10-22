## Worker report

### Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-finite-trivialize-invertible-upstairs.json`: item, statement unchanged, split into five steps following Stacks 0BUT.
- `dag/nodes/sec-six-functors-basics/lem-sfb-affine-invertible-finite-set-section.json`: one new statement-only lemma, unsplit; no Mathlib match.
- `citations.json`: seven step/node entries quoting the cited statements verbatim.

### Attachments

None for the item. Searches by its blueprint tag, by finite/trivialize/invertible combinations, and by the concept in `lean/WeilConjectures/AlgebraicGeometry` and `RingTheory` found no declaration stating the whole finite-map neighbourhood assertion. The existing `AlgebraicGeometry.Scheme.Modules.nonvanishing_section_trivializes` in `NonvanishingSectionTrivializes.lean:119` supplies a previously recorded dependency, not the item. No Lean was written or compiled.

### WANTED

None. All mathematical sources used are in the read clone.

### Findings and corrections

The item accurately states Stacks 0BUT, divisors-lemma-finite-trivialize-invertible-upstairs, so there is no statement dispute. Its source, statement, inherited NR searches, and provenance were retained. The item initially had no proof. I supplied the source's affine reduction and its explicitly suggested Properties 0F20 route to the nonvanishing section, instead of introducing the source's optional direct closed-point/global-section-exactness argument as extra dependencies.

The inherited blueprint ancestor chain terminates without an imported blueprint id (`blueprint_refs.py ancestor` returns None); I preserved that fact and the existing precise place/via chain, with an explicit sentence identifying 0BUT's section-selection step for the new node. No ancestor was invented and no unit/chapter record was changed. The new lemma has no other blueprint equivalent: whole-blueprint searches for `trivialize`, `invertible points`, `nonvanishing finite`, `0F20`, and `0BUT` were read. The current constructible-stability proof places the local lemma below the alteration/norm auxiliary route already recorded in the item; this split does not change that route.

### Unfinished work

The new section-existence node is intentionally unsplit. Its source 0F20 is obtained and its Mathlib searches are recorded as returned in searches.jsonl. There is no unfinished step in the item's proof.

## New nodes

`lem-sfb-affine-invertible-finite-set-section` is a genuine separate geometric lemma: it constructs one section on any affine scheme avoiding an arbitrary finite subset, without a finite morphism or a chosen base point. It neither asserts a neighbourhood downstairs nor restates a clause of the item. Source: Properties Tag 0F20, label lemma-quasi-affine-invertible-nonvanishing-section, with X affine and W=X. The stronger source conclusion that the section-open is affine is unnecessary and is not claimed. The new node contains no proof or proof dependencies. Its statement introduces X, L, E, s, the local ring, maximal ideal and residue field, with definition dependencies for affine schemes, invertible modules and residue fields.

LeanFinder was queried twice, once geometrically and once using invertible modules at finitely many primes. LeanSearch returned evaluation/basic-open facts for the structure sheaf. Loogle's initial sheaf identifier was unknown (reported literally); the follow-up `Module.Invertible, "exists"` returned a finite trivializing localization cover and an ideal representation with an extra Picard hypothesis. The grep searches returned no geometric simultaneous-section result and located the candidate algebraic facts. The returned types show that none is a one-line specialization: an independently chosen local basis at each prime does not choose one global generator at all specified primes; the fractional-ideal result needs a semilocal ring and a fractional-ideal presentation. None is mislabeled as a leaf. Inherited item searches likewise return finite fibres, finite restriction, local freeness and free loci, not the item.

## Not duplicates

lem-sfb-affine-invertible-finite-set-section vs lem-sfb-finite-trivialize-invertible-upstairs: the new 0F20 lemma chooses one global section avoiding an arbitrary finite set on an affine scheme; the item 0BUT constructs a neighbourhood in the target of a finite morphism over which an invertible sheaf upstairs is trivial. A finite set of points of an arbitrary affine scheme is not supplied as a fibre of a finite morphism by the item, and a neighbourhood trivialization does not choose the section asserted by the new lemma. The source field also mentions 0BUT only to locate its invocation of 0F20.

No existing node with source tag 0F20 or its source label was found by whole-DAG search. Title and statement searches for invertible sheaves, finite sets and nonvanishing, plus the whole-blueprint searches above, were read before writing the new node.

lem-sfb-affine-invertible-finite-set-section vs lem-sc-ample-finite-principal-affine: the existing 09NV lemma constructs a section of some positive tensor power of the given ample module; the new lemma constructs a section of the given arbitrary invertible module itself, on an affine scheme, without ampleness of that module.

lem-sfb-affine-invertible-finite-set-section vs lem-sc-ample-finite-set-affine: the existing 01ZY lemma produces an affine open containing the finite set but supplies no section of an independently specified invertible module.

lem-sfb-affine-invertible-finite-set-section vs lem-weil-pbc-nonvanishing-section-trivializes: the existing 01CY lemma starts with an already chosen section and proves openness and trivialization; it does not choose a section nonvanishing on a prescribed finite set.

## Review by NU

I read Divisors Tag 0BUT, label lemma-finite-trivialize-invertible-upstairs, statement and full proof at lines 3617–3652. Its hypotheses are exactly finite p and invertible M; no flatness, surjectivity, normality, Noetherianity or residue-field hypothesis is needed. I read Properties Tag 0F20, label lemma-quasi-affine-invertible-nonvanishing-section, statement and induction proof at lines 5327–5380. The new node specializes quasi-affine to affine and W to all X and retains the unpowered invertible sheaf. In particular E need not consist of closed points. I also read Modules Tag 01CY, label lemma-s-open, for the openness/trivialization assertion used by the existing dependency.

Step 1 cites and uses the actual statements of def-pc-scheme, def-weil-finite-integral-morphism and def-sc-invertible-module. The finite-morphism definition explicitly says inverse images of affine opens are affine and their section-ring maps are finite. This proves the restriction is finite directly, without an uncited base-change theorem. Restriction of a locally rank-one free module is locally rank-one free. Choosing an affine neighbourhood is the defining local property of schemes. This is an elementary reduction with its argument written out.

Step 2 cites lem-weil-pbc-finite-closed-map-finite-fibres, whose statement explicitly says the set-theoretic inverse image of every singleton is finite, and the new section-existence node, whose conclusion is literally nonzero image in every L_x/m_x L_x for x in the selected finite set. I opened both statements. The source X is affine by step 1 and L is invertible there, so every hypothesis of the new node is in force. This is a non-elementary step, with both inputs cited.

Step 3 cites lem-weil-pbc-nonvanishing-section-trivializes. I opened its statement, which defines X_s by s_x outside m_x L_x, proves it open and gives the actual multiplication-by-s isomorphism of restricted modules. Thus the nonzero residue values from step 2 give exactly E contained in W. No stalk merely being nonzero is confused with nonzero image in the residue fibre. This step is non-elementary and cites the theorem, rather than only the definition of invertibility.

Step 4 cites the same finite-morphism leaf, whose statement explicitly says images of all closed subsets are closed. Its application to C=X minus W gives q(C) closed in U. The proof then spells out why z is outside q(C) and why the inverse image of U minus q(C) is contained in W; these are elementary set arguments. There is no hidden shrinking or support theorem, and no claim that points of the original fibre are closed in X.

Step 5 restricts the isomorphism and its inverse from step 3, verifying the inverse identities by restriction. The equality of inverse images follows from V contained in U. This is elementary and does not assert a new restriction/comparison theorem. Every proof step is shorter than 500 characters, so there is no long step hiding a lemma. Every cited node has a verbatim statement quote in citations.json.

For edge cases I checked E empty (s=0 meets the new lemma), X empty (the unique section works), singleton and nonclosed points (explicitly allowed by 0F20), and arbitrary finite fields (no infinite-field avoidance is used). Empty fibres of a finite non-surjective morphism are handled by the same image-complement argument. For a globally trivial module, the section 1 works for every finite set. No reducedness or domain property appears: the residue-fibre formulation and 0F20 both allow nilpotents. An empty base has no z and the item is vacuous. These checks required no correction of the statements.

I checked delivery-errors B–E against these files: one self-contained statement-only node; correct tag/label; no proof hidden in that statement; searches actually logged; no Mathlib leaf claimed; blueprint places filled; existing nodes reused; each non-elementary input covered by a node that states it; no dependency on the item from the new node; no clause relabeled as a split; and all source hypotheses maintained. The only extra-unit non-Mathlib tool cited is the existing 01CY nonvanishing theorem, declared in split_report.tool_uses for the maintainer's judgement. This direct-delivery self-review is signed by NU under the user's instruction; no second worker or subagent was started.

### Dry-run repair

The first dry run noticed the contextual 0BUT tag in the new node source and requested the pair comparison with the item. I added the explicit difference above after re-reading both statements; no mathematical node or proof changed.
