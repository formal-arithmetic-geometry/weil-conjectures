# Stage-1 delivery: lem-sfb-dvr-nodal-chart-blowup-calculus

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-dvr-nodal-chart-blowup-calculus.json`: statement, split into 15 proof steps. Mathlib verdict: no exact match; the item is not a Mathlib leaf. All hypotheses and every clause of its statement are unchanged.
- No new nodes and no new Mathlib leaves. The proof uses 43 existing DAG nodes.
- `citations.json`: verbatim statement quotations for every citation of every proof step.
- `searches.jsonl`: the real search command's log. The inherited item searches are retained, and the searches made in this attempt are appended to the item's search record.
- `write_split.py`: sandbox-only reproduction of the JSON and citation files; it is not a project tool and is not part of the delivery.

## Attachments

None. I searched `lean/WeilConjectures/` for the blueprint tag, nodal and semistable terminology and the local-model notion. No project declaration there states the whole item with a completed proof. General deformation-space blowup declarations concern different centres and do not supply this statement.

## Literature wanted

WANTED: A. J. de Jong, *Families of curves and alterations* (1997), Lemma 3.13, printed p.609, for lem-sfb-dvr-nodal-chart-blowup-calculus. The archive is absent from local literature. I read the primary publication online at https://aif.centre-mersenne.org/item/10.5802/aif.1575.pdf (PDF p.11, printed p.609). Its proof invokes the local equation and rational exceptional curves; it does not give the calculations this item needs. The delivered proof is therefore explicitly agent-written, with the Stacks local-algebra and blowup input lemmas cited individually. No missing document was downloaded or written into the repository.

## What needed attention

The item was a statement-only node. There was no earlier sandbox split or report to preserve. The three blowup formulas were correct; they need to be proved in fraction subalgebras, since merely cancelling a factor in an unsaturated polynomial presentation can introduce a spurious component. I proved the required injections using a common Laurent normal form.

The nodal-geometric-fibre definition includes nonemptiness and connectedness, not just local singularity types. I checked both for the original model and for the blowup; the exceptional bridge connects the two strict transforms in the special fibre. The exponent-zero middle chart is a Laurent line, not an origin with a singularity. For n=3 the middle chart has exponent one and is regular, although its special fibre is nodal. These distinctions are retained explicitly.

The definition of normal ring requires normality at every prime localization, rather than just integral closedness of the global domain. The proof invokes localization normality after proving integral closedness. The etale assertion concerns stalk properties and pulled-back chart descriptions, not an equality of local rings or a rational residue-field hypothesis. The blowup-centre argument shrinks the common neighbourhood so the inverse image of o is exactly the chosen reduced point as a subscheme.

I caught and corrected an inaccurate tag in my draft's blowup-complement source place: the effective-Cartier/complement lemma is Tag 02OS, not Tag 080E. No statement correction or STATEMENT-DISPUTED case was necessary.

## Blueprint and route

I read the chapter record, the sk-thm-sf-ctf-stability unit, and the current main-20261015 direct-image blueprint node. This item supports clause (3), through the already recorded alteration/plurinodal and de Jong Lemma 3.13 route; it does not substitute a different direct-image or alteration argument. It is not the unit's key statement and does not change a unit record. `blueprint_refs.py ancestor` reports None for this inherited creation chain, matching its existing null `blueprint.from.node`; its detailed from.place and via chain are preserved. Searches of the whole blueprint for nodal, blowup, xy, and rational singularities found no blueprint node stating this package. `same_as` is consequently [].

The nonlocal facts used here are generic local-algebra and blowup tools. In particular the Nagata chart cover and flat comparison supply the actual ordinary blowup, while the regular/normal ascent and descent lemmas supply the stalk comparisons. Each off-unit dependency is declared as a tool use in split_report, with the steps that use it. None replaces a geometric step of the unit's route.

## Not duplicates

No new nodes were created. I reused the existing polynomial-normality, normal-localization, PID-normality, valuation-flatness, flat-height, etale-dimension, regularity, descent and Nagata blowup nodes instead of creating special cases or nodes for individual clauses of this item.

## Review by NJ

I checked the delivery-errors B--E cases against the actual statement, all cited node statements, and the source passages. I read de Jong Lemma 3.13 online for the item's geometric role; locally I read Stacks algebra.tex at the PID-normal, polynomial-domain-normal, normal-localization, Noetherian permanence, flat dimension, standard smooth, normal/regular ascent and faithful descent lemmas, more-algebra.tex at torsion-free-flatness and etale dimension, curves.tex at the nodal-family definitions, and divisors.tex at affine blowup charts and flat base change. There are no new statement-only nodes whose sources or small cases remain to be checked.

For step 1 the polynomial and DVR definitions justify finite normal forms and the Laurent embedding. The integral-scheme definition is used only after the zero prime is generic and the stalks are domains. I checked that the same coefficient argument works with exponent zero, which is needed later and is not covered by an implicit n>=1 induction.

For step 2 PID-normality supplies precisely Noetherianity and a normal domain; finite-type-Noetherianity applies to the displayed finite presentations. The torsion-free-flat lemma really has a valuation-ring hypothesis, supplied by the DVR definition. Torsion freeness follows from the injection, without supposing the nodal algebra is smooth. Localization Noetherianity is justified directly by extending ideals.

For step 3 the polynomial-normal and normal-localization statements apply to domains and to multiplicative sets not containing zero. The Laurent coordinates are nonzero. I checked the signs: for exponent i the second Laurent ring requires c_i in pi^(-ni)R, so negative powers of X have exactly the required pi-divisibility. An integral element satisfies the same monic equation over both over-rings. This proves normality without invoking Serre's criterion, completeness or excellence.

For step 4 the polynomial-line dimension lemma supplies dimension one. The nodal definition is read in full, including connectedness. The axes intersection and coefficientwise completion are explicit, so I do not cite a definition node as if it were a nodality theorem. The square-zero lifting argument verifies smoothness away from the possible node directly from the smooth definition.

For step 5 the cited flat-height statement has the local dimension formula as an explicit equivalent assertion. Both rings are Noetherian and the map is flat by step 2. The special-fibre local ring really is k[x,y]/(xy) localized at its origin, and has a strict chain of length one. I did not confuse fibre dimension at a point with the dimension of the total local ring.

For step 6 the regular definition and DVR dimension give regularity of R; regular-local localization makes it a regular ring. The Laurent presentation has an invertible Jacobian entry and is standard smooth, so standard-smooth-is-smooth followed by regular ascent applies with the hypotheses checked. At o, the calculation distinguishes n=1 from n>=2: in the latter case the equation has no linear term in pi,x,y, so the cotangent dimension is three while the ring dimension is two. This includes mixed characteristic and residue characteristic two.

For step 7 smoothness has the affine smooth-ring interpretation explicitly stated in the cited definition. Regular ascent and regular-implies-normal apply to those affine rings. Smooth-flat supplies flatness and local finite presentation. The same flat dimension formula and the pure-one-dimensional fibre prime chains give the asserted two-dimensional special-fibre stalks. Nothing requires the smooth scheme to be globally affine, nonempty or quasi-compact.

For step 8 the cited Nagata statement really supplies a cover by the fraction subalgebras for the three generators of I. The chart-ring definition identifies the fractions. I prove injectivity as well as surjectivity of each displayed presentation: y/x=x^(n-2)t^n in the x-chart and rs=pi^(n-2) in the middle chart. This is why n>=2 is required. The Proj and homogeneous-fraction definitions identify the chart coordinates used on overlaps, rather than appealing to unspecified overlap maps.

For step 9 the previous calculations establish the geometric properties chart by chart, including exponent zero and one. I explicitly verified connectedness from the overlaps and the exceptional bridge. Regularity is deduced from the previously proved regularity calculation, with the possible singular origin only when n>=4. This is an application of previous steps, not an independent hidden resolution theorem.

For step 10 the inverse-image ideal is computed, not inferred from a set-theoretic support. In the outer charts it is (x) and (y), and in the middle it is (pi). The standard Proj open for a second generator is D(b/a) on the first chart because that homogeneous fraction is invertible there. The resulting overlap formulas are computed before restricting to the exceptional fibre.

For step 11 the P1 definition gives precisely two affine lines with reciprocal coordinates. The middle hyperbola is their common overlap for n=2. I checked all three conic coordinate formulas and checked that the X- and Y-opens cover, including characteristic two. For step 12 each axis in the middle chart completes with one outer chart to P1; the two components meet once, and the outer charts have no exceptional overlap for n>2. These are explicit gluing arguments with no genus-zero-to-P1 theorem hidden in them.

For step 13 the affine complement statement really says isomorphism away from the centre. The flat comparison's definition gives its exact source and target, and the cited theorem makes that particular comparison an isomorphism. Etaleness supplies its required flatness. Taking a fibre therefore extends coefficients to the chosen residue field and then its algebraic closure; no arbitrary-base-change assertion for blowups is being used.

For step 14 I read every ascent/descent statement: etale base change remains etale; etale algebras are flat; induced stalk maps are flat and local; flat local maps are faithfully flat. Normal ascent is applied after base-changing to the base stalk, not by assuming a whole neighbourhood normal from one normal stalk. Regular ascent likewise uses the regular-local-localization lemma on that base. Faithful normal and regular descent use the actual stalk map. The etale local-dimension lemma states the equality needed in both directions. This proves the common-neighbourhood claim without assuming the two residue fields agree.

For step 15 the etale fibre over k is first shown Noetherian, zero-dimensional and normal. Minimal-prime finiteness is actually stated by its cited node. Thus it has finitely many points and can be shrunk to the chosen one. Its local normal domain of dimension zero is a field, so the remaining subscheme is the reduced point. Only after this check is the flat blowup comparison applied to that centre. This repairs the potential gap between an inverse-image centre and a single reduced-point centre.

I tested n=1, n=2, n=3, and n=4 explicitly; I also checked the auxiliary exponent-zero chart, the empty smooth scheme, arbitrary residue fields and residue characteristic two. No excellence, perfection, completeness or characteristic-zero fact is used. There are no proof steps over 2000 characters. The verbatim quotations in citations.json are whole cited statements, so a reviewer can assess every step against what its dependency actually says.

## Checks and unfinished work

The first server review_split check passed with 0 new nodes. The required full delivery dry run and push follow this self-review. No mathematical clause is left unfinished; this is a natural-language split only, with no Lean writing or compilation.
