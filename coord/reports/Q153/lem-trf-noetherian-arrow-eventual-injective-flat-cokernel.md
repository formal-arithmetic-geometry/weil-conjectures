## Worker report

Files written: dag/nodes/sec-trace-formula/lem-trf-noetherian-arrow-eventual-injective-flat-cokernel.json (statement, split; no Mathlib match), citations.json and this report. Existing search records in the live item are retained and the five searches run for Q153 are appended. No new nodes or Mathlib leaves.

Attachments: none. Project-source searches for the item tag and eventual injectivity/flat cokernels found no declaration of the whole item. The project does have RingTheory.exists_flat_stage (WeilConjectures/RingTheory/ColimitEventuallyFlat.lean:74) and flat_mod_injective (WeilConjectures/RingTheory/FlatModInjective.lean:235), which are ingredients, not an attachment for the item.

WANTED: none.

The item statement is unchanged and needs no dispute. The subtle point is the quantifier: Tag 00R6 gives one flat stage, whereas this item needs a whole upper tail. Step 2 supplies the missing argument by applying the already existing 00MO node with ideal zero. Also the final fibre argument only needs injectivity of the source comparison; it imposes no injectivity on the target comparison. Nothing remains unfinished.

## Searches and reuse

Read the whole current item and its parent lem-trf-valuation-general-mod-injective, the chapter sec-trace-formula and unit sk-i-curve-zero. Read the current main-20261015 blueprint node lem-trf-local-term-locality. Its broad contracting-correspondence route is unchanged: this is the already isolated 046Y commutative-algebra helper along the inherited valuation-ring branch, not a replacement of the unit proof.

Searches of the whole DAG by tags 00R6, 00ME and 00MO and by flatness, localization and field-extension keywords found the three existing algebra lemmas cited below. tools/blueprint_refs.py ancestor returned lem-trf-local-term-locality. Whole-blueprint searches for 'eventually flat', 'flat cokernel', '00R6' and 'eventual injectivity' found no matching imported node; 'scalar extension' found the existing vector-space scalar-extension definition, which is reused. Existing project declarations were read in ColimitEventuallyFlat.lean and FlatModInjective.lean. No new statement is needed.

The recorded Q153 Mathlib searches were all run through msearch.py. LeanSearch found flatness criteria and localization stability; Loogle returned no hits for Module.Flat, IsLocalRing, Function.Injective; grep returned no stage/cokernel hit in RingTheory; two LeanFinder phrasings found completion theorems, local detection of injectivity and flatness criteria. Their signatures are individual ingredients, and none asserts the varying-ring eventual stage/limit result. All five services returned answers this time. The older unavailable LeanSearch entry is retained as history of a genuinely unavailable earlier search. No searches were fabricated.

## Not duplicates

No new nodes. The existing lem-weil-pbc-colimit-eventually-flat gives one flat target stage; lem-weil-pbc-flat-another-variant-local-criterion gives flatness across one localized base-change square; lem-weil-pbc-flat-mod-injective gives injectivity and cokernel flatness for one Noetherian local map. They do not separately assert the item. Reusing them avoids duplicate nodes for these ingredients or the item's clauses.

## Review by Q153

I read Algebra Tag 046Y (lemma-mod-injective-general), first and final proof paragraphs, Tag 00R6 (lemma-colimit-eventually-flat), Tag 00MO (lemma-another-variant-local-criterion-flatness), and Tag 00ME (lemma-mod-injective) in literature/stacks-project/algebra.tex, and checked their labels against tags/tags. No SGA source is used. There are no new nodes requiring a separate source review.

Step 1 cites the statement of lem-weil-pbc-colimit-eventually-flat, not its proof: it states existence of one flat stage for exactly these finite Noetherian local systems, localized tensor-product ring transitions and canonical module base changes. I matched its A, B, N with R_i, S_i, N_i and its limit action with the given semilinear cocone. Its extra forgetful-functor preservation hypothesis follows from the item's explicit stage-representative/eventual-equality description: maps out of that quotient are exactly compatible maps of the underlying sets. No unmentioned essential-finite-type hypothesis is needed by the DAG node.

Step 2 cites the full statement of lem-weil-pbc-flat-another-variant-local-criterion. At indices a and j all four rings are Noetherian local, all four arrows local, and the specified square commutes. The given localization and module base-change maps are precisely its maps. With I=0 the quotient-flatness hypothesis is flatness at a and the source of its kernel comparison is zero, so no Tor vanishing is silently assumed. Zero is proper in a local ring. This gives a whole upper tail without applying the existence-only 00R6 statement as if it already gave eventual flatness. Flatness is transported along the given linear isomorphism, an immediate invariance of its injectivity-of-tensor definition.

Step 3 opens and cites def-weil-vector-space-scalar-extension, whose statement explicitly says that the tensors of a basis are a basis, including arbitrary-dimensional spaces. It is therefore strong enough to prove x maps to x tensor 1 injective. The local cocone map contracts the maximal ideal exactly, giving the residue-field map. A unital map between fields has zero kernel, so the coefficient calculation is valid; the zero vector space has the empty basis and causes no exception. The assumed Psi_j is injective because j is above i_1. This is a short elementary basis calculation, not an additional descent lemma.

Step 4 uses only the given cocone identity and quotient definitions. Locality ensures r_j(m_j) lies in m and semilinearity makes the maps on quotient modules well defined. Evaluating on [x] proves the commutative square. A kernel element of the stage fibre arrow maps to zero under the injective composite of the source comparison and the limit fibre arrow. The target comparison beta_j is not required to be injective; no inference cancelling beta_j is made.

Step 5 opens the statement of lem-weil-pbc-flat-mod-injective and swaps its module letters carefully: its finite source N is our M_j, its flat target M is our N_j. Its ring S only needs to be Noetherian; the item provides this and more. Its map need only be R_j-linear, which follows from S_j-linearity. It states both injectivity and flatness of the quotient, so the citation covers both remaining clauses without a hidden exactness or cokernel lemma.

I checked the small cases: a singleton diagram reduces to 00ME; M_j=0 gives the already established target flatness; N=0 forces the source fibres to vanish using Psi and the limit fibre hypothesis, so 00ME applies without a nonzero-module assumption. A non-linearly-ordered directed index set is handled by taking an upper bound of a and i_1, never a maximum. All objects remain in the sufficiently large universe already allowed by the item. All five steps are shorter than 2000 characters. The complete proof is 2660 characters and adds no hidden comparison theorem. citations.json contains verbatim statement text for every step citation. This self-review corrected the potential existence-versus-eventual gap before delivery; no source or statement correction was needed.

The three algebra statements are declared generic off-unit tools in split_report.tool_uses. Their role is exactly the algebra input used by 046Y; they do not replace any higher blueprint route. The vector-space scalar-extension citation is a definition.
