## Worker report

The module states that pseudo-coherence is preserved by a binary direct summand in the
scheme derived category. It defines no new notions and leaves the theorem proof as
`sorry`, as required for stage 2.

The scheme hypothesis is rendered by `(X : Scheme.{u})`, using Mathlib's
`AlgebraicGeometry.Scheme` (the `def-pc-scheme` dependency). The derived-category
hypotheses are the shared localization instance
`[HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]` and,
for every open `U : X.Opens`, the corresponding localization instance on
`(moduleRings X.toRingedSpace).over U`, exactly as in `def-pc-derived-category` and
`def-pur-pseudo-coherent-complex`.

The three objects `K`, `L`, and `M` are all explicit binders of
`schemeDerivedCategory X`, so they are objects of `D(𝒪_X)`. The direct-sum clause is
rendered as `h : Nonempty (K ≅ L ⊞ M)`, i.e. an isomorphism from `K` to the categorical
binary biproduct of `L` and `M`. The hypothesis that `K` is pseudo-coherent is
`hK : IsPseudoCoherent X K`. The conclusion is the conjunction
`IsPseudoCoherent X L ∧ IsPseudoCoherent X M`, stating the result for both summands.
No extra assumptions are introduced; zero objects and zero summands remain allowed by
the categorical biproduct and by the definition of pseudo-coherence.

Dependency declarations used:

- `AlgebraicGeometry.Scheme` from `Mathlib.AlgebraicGeometry.Scheme` for `Scheme`.
- `AlgebraicGeometry.schemeDerivedCategory` from
  `Sheaf.AlgebraicGeometry.DerivedCategory` for `D(𝒪_X)`.
- `AlgebraicGeometry.Scheme.IsPseudoCoherent` from
  `Sheaf.AlgebraicGeometry.PseudoCoherentComplex` for pseudo-coherence.

Searches made: `msearch.py leanfinder` for “direct summand of a pseudo-coherent complex
is pseudo-coherent” (generic K-projective and derived-category hits, no match);
`msearch.py loogle` for `PseudoCoherent direct summand` (unknown identifier, no
match); `msearch.py grep` for `pseudo.?coherent.*summand|summand.*pseudo.?coherent`
in Mathlib (no matches); `rg` over `WeilConjectures/` and `lean/Sheaf/` (no existing
scheme-level summand theorem; only unrelated ring-level pseudo-coherence declarations);
and `grep -rl` over `dag/nodes` (no duplicate target declaration).

Edge cases checked: `L` or `M` may be a zero object, and no nonemptiness or finiteness
condition on the scheme or the biproduct index is present. The universe `u` is shared
by the scheme, its module category, and all three derived objects; `w` is the derived
localization universe, matching the dependency declaration.

## Second reading by E1

I independently read the item node, its three statement dependencies and their actual
declarations, and the delivered module. The repository has no local Stacks checkout;
I read the Stacks TeX and tag table in `/home/ubuntu/c1-stacks-review/` instead:
`cohomology.tex`, `lemma-summands-pseudo-coherent` (08CE), its section introduction
and definition (08CB); `perfect.tex`, `lemma-pseudo-coherent` (08E5) and
`lemma-pseudo-coherent-affine` (08E7); and `more-algebra.tex`,
`lemma-summands-pseudo-coherent` (064X). Tag 08CE assumes a ringed space, with no
Noetherian, separated, quasi-compact, characteristic or base-field assumptions.
Its pseudo-coherent clause applies to the scheme case stated by this node; the
source's additional m-pseudo-coherent clause is not a clause of this node.

The complete object/hypothesis/conclusion inventory and its Lean rendering is:

| Node item | Lean rendering | Verdict |
| --- | --- | --- |
| An arbitrary scheme X | `(X : Scheme.{u})` | Exact; Mathlib's locally affine locally ringed space, as recorded by `def-pc-scheme`. |
| Three objects K, L, M of D(O_X) | `(K L M : schemeDerivedCategory X)` | Exact; the dependency abbreviation is `DerivedCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace))`, not D_QCoh or a bounded subcategory. |
| K is isomorphic to L direct-sum M | `(h : Nonempty (K ≅ L ⊞ M))` | Exact; Mathlib's notation is `biprod L M`, the binary categorical direct sum. Existence of an isomorphism is sufficient; no chosen decomposition is demanded. |
| K is pseudo-coherent | `(hK : IsPseudoCoherent X K)` | Exact; uses `AlgebraicGeometry.Scheme.IsPseudoCoherent` from the recorded dependency module. |
| L is pseudo-coherent | First factor of `IsPseudoCoherent X L ∧ IsPseudoCoherent X M` | Exact. |
| M is pseudo-coherent | Second factor of that conjunction | Exact; both conclusions occur together under the same hypotheses. |

The dependency definition of pseudo-coherence quantifies over every point, choosing
an open neighbourhood, a cochain complex with an integer upper bound, finite-free
terms of degree-dependent finite ranks, and an isomorphism to the derived restriction
of E. I read its full body, including the use of `SheafOfModules.overFunctor`,
`DerivedCategory.Q`, and `ULift.{u} (Fin r)`. There is no data sorry or private notion.
This matches the node's local finite-free definition. The only instance binders in
the delivered theorem are the shared global and open-site `HasDerivedCategory.{w}`
choices required by these dependency signatures. Mathlib's DerivedCategory/Basic
explains them as localization choices and provides `HasDerivedCategory.standard`;
they impose no geometric property. The theorem uses the existing Abelian structures
and does not choose a second module-category structure or derived category.
All objects precede the two hypotheses, and both conclusions use those same objects.

Edge cases: the empty scheme is permitted (`∀ y` in pseudo-coherence is vacuous);
K, L and M may be zero, including either or both zero summands. Finite ranks may be
zero because the definition uses `r : ℕ` and `Fin r`. A binary sum has no arbitrary
index-set binder, so the empty-index issue does not introduce any condition here.
There is no degree n to restrict to positive values; the definition ranges over all
integer degrees. Arbitrary residue characteristics and non-Noetherian schemes are
included. Universes `u w` are explicitly bound, with the same sheaf carrier and
localization universe throughout the dependencies; no independent test-object
universe or restriction to a field is present.

Independent searches, with different formulations from the first reader:

- `msearch.py leansearch`: “Pseudo-coherence of both factors of a binary biproduct in
  the derived category of sheaves of modules”; service returned Internal Server Error,
  recorded as unavailable, not used as negative evidence.
- `msearch.py leanfinder`: “A retract of a pseudo coherent object in the derived
  category of a scheme is pseudo coherent”; eight generic derived T-structure
  declarations, no pseudo-coherent summand theorem.
- `msearch.py loogle`: quoted name fragment `"PseudoCoherent"`; zero hits.
- `msearch.py grep`: `coherent.*(retract|biprod)|((retract|biprod).*coherent)`;
  zero Mathlib hits.
- Direct `rg` of Mathlib, `WeilConjectures/` and repository `lean/Sheaf/` for
  `pseudo.?coherent|pseudocoherent`, and of the project/source for the above
  retract/biproduct expression: the scheme definition is the recorded dependency,
  the ring-level definitions have a different carrier, and the coherent sheaf
  kernel/cokernel/biproduct theorem concerns modules rather than derived objects.
  No exact existing theorem was found. The proposed full declaration name is
  absent from `dag/lean_names_upstream.json` and the project/source searches.

Mismatch found: H8, the original theorem docstring only said “reduces locally to the
affine module criterion and the ring-level direct-summand lemma”. It omitted the
node's essential quasi-coherent cohomology justification for the summands, the
additive affine equivalence, the two applications of the affine criterion, and
the local-to-global conclusion. I replaced only that docstring with a four-step
proof carrying all those arguments and all four named proof dependencies.
No signature, node statement, hypotheses, conclusion, imports or definitions changed.
There are no new nodes, dependency modules or statement corrections to review.
The sole theorem proof remains `sorry`; every universe and variable is bound.
The node's recorded signature agrees verbatim after whitespace normalization.

Validation: `scompile.py` compiled the repaired module on the server in 2.1 seconds,
exit code 0, with no warnings. The signature comparison and 100-character Lean line
check passed. `deliver2.py --no-push` printed OK: the delivery compiles and passes
the stage-2 preflight.
