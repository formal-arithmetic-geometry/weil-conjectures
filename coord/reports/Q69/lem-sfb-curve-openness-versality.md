# Q69: lem-sfb-curve-openness-versality

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-curve-openness-versality.json: statement unchanged; split into four proof steps.
- dag/nodes/sec-six-functors-basics/lem-sfb-artin-square-zero-effectivity-openness.json: new statement, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-proper-space-square-zero-effectivity.json: new statement, unsplit; no Mathlib match.
- citations.json: verbatim statement quotations for every node cited in every item step.

The search records and actual returned hits are retained in searches.jsonl and the three *-search-results.json files. No Lean file, compiler, Lake command, repository write, or direct git command was used.

## Attachments

None. Searched the live project's WeilConjectures source for the item tag, versal/Versal/Versality, strong effectiveness, square-zero systems, SGE and RimSchlessinger. No declaration states the item or either new input. Existing sorry declarations were not treated as finished proofs.

## Literature wanted

None. All sources are in the supplied Stacks checkout.

## Problems and corrections

No statement dispute. The imported item is a statement-only prerequisite created for the nodal-curve-stack split, not a proof. Its existing sources, searches, created metadata and blueprint provenance are retained. The blueprint ancestor command prints None for this imported created-node chain; the null from.node and full inherited via list are retained, rather than inventing an ancestor.

The terse proof of Stacks 0D59 cites the fully faithful inclusion in the proper-space groupoid and 0D3X. This delivery expands the actual route of 0D3X: the Artin 0CXU strong-effectivity criterion. It does not use algebraicity of the curve stack (which depends on this item), and does not replace the argument by a new node restating openness for all proper spaces. The two new inputs have distinct mathematical tasks: one is an abstract criterion, the other constructs an effective family over the inverse-limit ring without any versality assertion.

During the citation audit I identified the affine-pushout identification as an input that must not be left implicit. I added the existing lem-sfb-affine-closed-pinching-pushout rather than creating a duplicate. Its hypothesis is just a surjective ring map, so it applies to B' -> B even though A -> B need not be integral. I specifically did not use lem-sfb-ferrand-scheme-pushout, whose integral-map hypothesis need not hold here.

## Unfinished work

Only the intended one-level children remain unsplit. The effectivity child is the concrete construction in the proof of 0D3X, not the general formal effectivity of all proper spaces (which the source warns is false). Its future split should follow the structure-sheaf extension, derived inverse limit, quasi-coherent replacement, thickening, flatness and deform-property arguments in that proof. This is distinct from curve formal effectivity for powers of a maximal ideal in a complete Noetherian local ring.

## Not duplicates

No existing node with either new input's tag (0CXU or 0D3X) was found. The item and the other curve-stack prerequisites mention 0D59, which is a different lemma.

lem-sfb-proper-space-square-zero-effectivity vs lem-sfb-curve-formal-effectivity: the new node treats arbitrary rings and inverse sequences with every composite kernel square zero, with arbitrary-dimensional proper algebraic spaces; the old node treats a complete Noetherian local ring and its powers-of-maximal-ideal tower for curves. Neither is the other's stated special case.

lem-sfb-artin-square-zero-effectivity-openness vs lem-sfb-artin-representable-diagonal-criterion: the new node concludes openness from square-zero strong effectivity; the old criterion assumes openness and concludes algebraicity from different effectivity and tangent-space conditions. It cannot prove this item without circularity.

## Review by Q69

I read the item against quot.tex Situation situation-curves, equation-curves-over-proper-spaces and Lemma 0D59, and read the complete proof of 0D3X to choose its actual strong-effectivity route. I read artin.tex Lemma 0CXU and Remark remark-strong-effectiveness, the definitions of (RS*), limit preservation, versality and openness of versality. I read the chapter and unit records; the item is an auxiliary input to the curve-moduli prerequisite under the alteration input in the constructible direct-image route. Nothing in the unit's statement or steps changes.

For the new Artin criterion I checked all four assumptions of 0CXU, specialized only its base to Spec Z, and wrote each assumption and the Artinian lifting meaning of its conclusion explicitly. The arbitrary groupoid is described through pullback functors with their coherences. Its limit-preservation assumption includes arrows and eventual equality, not just descent of objects. Its tower condition requires square-zero kernels for every composite, not merely for successive maps. The Isom-presheaf condition is the representable-diagonal condition of the cited lemma. It does not assume an atlas or openness in its premises.

For the proper-space effectivity node I read every paragraph of the construction in 0D3X, from the square-zero tower through the final deform-property invocation. The source constructs a flat proper finitely presented algebraic space with identifications recovering the given entire system. The node states exactly this construction, without adding Noetherianity, projectivity, dimension, or uniqueness. I did not mistake the source's warning about unrestricted formal effectiveness for a failure of its square-zero theorem. Morphism properties for algebraic spaces are explicitly described on etale charts, with properness spelled out, instead of citing scheme-only definitions as though they defined space morphisms.

For step 1 I opened all four cited statements. The curve descent/Isom node actually gives the stack and the representable Isom sheaf. The affine pinching node actually states the scheme pushout for an arbitrary second ring map and surjective first map, so swapping product coordinates yields the required Spec(A x_B B'). The curve infinitesimal-pushout node allows every thickening and affine second morphism, so a square-zero closed immersion and a map of affine schemes meet its hypotheses, and its conclusion preserves the chosen overlap isomorphism. The curve limit node actually gives the equivalence of groupoids and all three descent/equality clauses. None of these claims is taken from a proof hidden behind a cited statement.

Step 2 cites only the newly stated proper-space effectivity construction. I verified flatness, properness, finite presentation, cartesian transition isomorphisms, the cocycle data and every composite square-zero kernel. This produces the actual total space and compatible reductions, rather than just an isomorphism class.

Step 3 has no external theorem hidden in it. Recursive lifts along a countable sequence prove surjectivity R -> R_1. Coordinatewise multiplication proves the kernel is square zero. A map to a field kills this kernel, so each geometric fibre is literally a base change of X_1 to that same algebraically closed field. The displayed associativity of fibre products gives the fibre identification; no upper semicontinuity, dimension invariance under arbitrary field extensions, projectivity theorem or formal algebraization is invoked. Fullness of the curve groupoids retains all the reduction isomorphisms. These are the elementary checks that transfer the ambient constructed object into the curve groupoid.

Step 4 cites the new Artin criterion and checks its four hypotheses against the previous three steps. Its Artinian lifting property agrees with the item's, including extension of the specified isomorphism, and its test bases and finite type points agree. The resulting open neighbourhood is exactly what the item asserts.

I tested the new statements and the argument on a constant tower, on towers R_n = k direct-sum M_n with square-zero multiplication on M_n, on empty families, zero rings (empty spectra), disconnected curves and dimension-zero proper families. The empty and zero-ring cases remain valid; if R_1 is zero, surjectivity with square-zero kernel forces the relevant rings to be zero. Ordinary towers k[t]/(t^n) do not satisfy the all-composite-square-zero hypothesis, so no claim of strong effectivity for those arbitrary towers is being smuggled in. The argument never requires fibres to be nonempty, pure one-dimensional, smooth or nodal.

I checked B through E of delivery-errors: the children have statements only and no proof sketches, their objects and specialized meanings are introduced, sources have the correct Stacks tags and labels, dependency quotations are literal statement substrings, and new nodes do not repackage the item or its clauses. No new proof step exceeds 2000 characters. I searched the whole DAG, the blueprint reference tool and the current project source before writing the two children. Mathlib searches used only the required msearch command: two semantic phrasings, Loogle, grep and LeanSearch for each new node and for the item. Returned universal-open and finite-type inverse-limit mapping results, effective epimorphisms, ring derivations and formal smoothness do not state either deformation-theoretic input; all search services answered, and neither child is a Mathlib leaf. No SGA source is used. All proof dependencies are in the item's unit, so no off-unit tool declaration is needed.

The server review_split check passed before report creation. The full required deliver.py dry run and push follow this signed review; any diagnostics are repaired in the sandbox.
