## What changed

Proved `AlgebraicGeometry.Scheme.finite_normal_dense_etale_stalk_goingDown` without changing
its signature or visibility. Added two proved auxiliary modules:
`Sheaf.AlgebraicGeometry.Morphisms.DenseEtaleStalkMapInjective` and
`Sheaf.AlgebraicGeometry.Morphisms.FiniteStalkIntegralDomainFactorization`.

The first proves injectivity using density, faithful flatness on the etale open,
and injectivity of germs on an integral target component. The second constructs
the intermediate domain as the image of the localized finite affine algebra in
the source stalk. It proves integrality by mapping monic equations, and flatness
of the inclusion using the quotient-algebra flatness theorem
`Algebra.FormallyUnramified.flat_of_restrictScalars`. The target combines normal
integral going down, flat going down and `Algebra.HasGoingDown.trans`.

All three modules compile without warnings. Explicit `#print axioms` for all three
public theorems reports exactly `propext`, `Classical.choice`, and `Quot.sound`.
No public import, existing statement, definition or other group's module changed.
The node proof and proof dependencies now describe the actual proof. The unit
`sk-prop-input-spreading` and its realized steps are unchanged.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.finite_normal_dense_etale_stalk_goingDown`
(node `new-finite-normal-dense-etale-stalk-going-down`).

Also completely proved the new public declarations:
`AlgebraicGeometry.Scheme.dense_etale_stalkMap_injective_of_domain_stalks`
(node `new-dense-etale-stalk-map-injective-of-domain-stalks`) and
`AlgebraicGeometry.Scheme.finite_stalk_integral_domain_factorization`
(node `new-finite-stalk-integral-domain-factorization`).

No holes added or left in any delivered module. This is a proof, not a decomposition.
The target's transitive axiom check contains no `sorryAx`.

## No longer needed

Removed the proof imports `Sheaf.AlgebraicGeometry.NormalSectionsFiniteProduct`
and `Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen`.
The original dependency `lem-sbc-normal-sections-finite-product` is unnecessary
for this proof and has been removed from the item's `proof_deps`. Normal component
product section rings, componentwise dominance, and openness of etale images are
not needed. Neither new auxiliary module imports the normal-product module or
UniversallyOpen. The old proof-dependency IDs `def-weil-etale-morphism` and
`def-weil-finite-integral-morphism` are also absent from the new direct
`proof_deps`: their uses now occur in the two auxiliary nodes. Finiteness and
etaleness remain statement imports of the item.
No claim is made that the removed node is unreachable from other targets.

## Where the brief, the DAG or earlier work was wrong

The previous attempt used a false flatness reduction for the entire stalk map;
that reduction and its second-reading text have been discarded. The current proof
uses flatness only for the inclusion of the image algebra into the source stalk,
which is proved in Lean. It does not claim that f itself or its stalk map is flat.

The DAG's original normal-component decomposition is a valid longer route, but
it is unnecessary below the unit level. The shorter factorization requires only
finiteness and a domain source stalk. The injectivity argument requires only
local Noetherianity and domain target stalks, plus density and etaleness; it uses
neither source normality nor finiteness. All the original target hypotheses remain.

Edge cases checked: the intermediate integral map may have a kernel, so the
factorization does not assume dominance. The range algebra is a domain because
it is an actual subring of the given domain stalk. Empty sources have no x.
The connected component selected in the injectivity proof contains f(x), so it
is nonempty and its source preimage contains x. Source density restricts along
an open inclusion without requiring global surjectivity or connectedness.

## New nodes

`new-finite-stalk-integral-domain-factorization`: the fully proved finite affine
localization and image-algebra factorization, in
`lean/Sheaf/AlgebraicGeometry/Morphisms/FiniteStalkIntegralDomainFactorization.lean`.
Its source is the original node's affine localization steps and the explicit
Mathlib integral-localization and quotient-flatness theorems. The chosen algebra
is constructed as a range subring, never chosen from an unproved existence theorem.

`new-dense-etale-stalk-map-injective-of-domain-stalks`: the fully proved dense-flat
germ argument and open integral component reduction, in
`lean/Sheaf/AlgebraicGeometry/Morphisms/DenseEtaleStalkMapInjective.lean`.
Its source is the original node's component and dense etale steps and the proved
source-library component and Mathlib germ theorems. Searches found ingredients
but no matching theorem; LeanSearch was unavailable. No change record is needed.

## Second reading by U2

1. Compared the existing target module and node with the repository versions.
   The entire theorem signature, visibility, existing docstring, and public imports
   are byte-for-byte unchanged. Only proof imports and the proof body changed;
   the existing node changes only proof, proof_deps, and proof_origin. The other
   two modules and nodes are new. No definition or statement change record is needed.
   Verdict: pass.
2. Compiled all three modules in import order using lcompile.py: no errors or
   warnings. Scanned for forbidden declarations and sorry: none. Independently
   compiled scratch copies with explicit #print axioms for all three public
   theorems: each reports only propext, Classical.choice, and Quot.sound.
   The private helper is covered transitively by the injectivity theorem.
   Verdict: pass.
3. No statements are split off with sorry. Read both fully proved auxiliaries
   and their docstring arguments. Checked the empty-source case, the nonempty
   selected target component, density after open restriction, and the possibility
   of a kernel in the integral factorization map. The intermediate domain is
   the constructed range subring; there is no choice from an unproved existence
   theorem. Independent LeanFinder searches used dense flat source subsets and
   finite local ring factorizations; Loogle confirmed the quotient flatness
   theorem. Searched the project and Mathlib for alternative germ and stalk
   factorization results. Only ingredients were found, not a duplicate result.
   Verdict: pass.
4. Read the proof from the target downward: normal integral going down and flat
   going down are combined by transitivity; injectivity and domain factorization
   supply exactly the missing inputs. Checked each import against the proof or
   public statement. The obsolete component-product and universally-open imports
   are removed, and every removed old direct proof dependency is listed above.
   The unit sk-prop-input-spreading, its steps, and realized fields are unchanged;
   this item refines a subargument below the unit level. Verdict: pass.
5. Read all three delivered nodes and checked their Lean statement records,
   proof steps, proof_deps unions, proof_origin, sources, searches, creation and
   blueprint records. The target dependencies name both auxiliaries and the two
   Mathlib going-down results; the auxiliary records describe the actual affine
   localization and dense-germ arguments. Verdict: pass.

Second reading changed only this report: added the independent review and made
the removed direct proof-dependency IDs explicit. No Lean or node repair was
needed. One original hole closed, zero holes added, zero split-off holes.
