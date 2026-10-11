## Worker report

The module `Sheaf.AlgebraicGeometry.Modules.ZeroLocusLocallyPrincipal` states
`AlgebraicGeometry.Scheme.Modules.Hom.isLocallyPrincipal_zeroLocus_of_isInvertible`.
Its only proof is `sorry`; no definition is introduced and no statement is corrected.

Hypothesis and conclusion correspondence:
- “Let X be a scheme” is `{X : Scheme.{u}}`, with explicitly declared `universe u`.
- “M and N are O_X-modules” is `{M N : X.Modules}`. The module category's arrows
  are O_X-linear sheaf morphisms.
- “M and N are invertible” is `[M.IsInvertible] [N.IsInvertible]`, using precisely
  the dependency's recorded `Scheme.Modules.IsInvertible` class.
- “Let φ : M → N be an O_X-linear morphism” is `(φ : M ⟶ N)`.
- “The zero locus φ.zeroLocus is locally principal” is
  `φ.zeroLocus.IsLocallyPrincipal`. The existing zero-locus ideal-sheaf definition
  and existing locally-principal predicate are used verbatim. The latter means
  every point has an affine neighbourhood on which the ideal is principal.

Dependency declarations read and used:
- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`,
  `Mathlib.AlgebraicGeometry.Scheme`, including full signatures and docstrings.
- `def-sc-invertible-module`: `AlgebraicGeometry.Scheme.Modules.IsInvertible`,
  `WeilConjectures.AlgebraicGeometry.Modules.Invertible`, including its full
  class definition and `exists_isoUnit` field. It expresses local rank-one
  triviality; quasi-coherence follows, rather than being an additional binder.
Both modules are publicly imported through the sole used import
`WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus`.
The conclusion also uses `AlgebraicGeometry.Scheme.Modules.Hom.zeroLocus` in that
module, and `AlgebraicGeometry.Scheme.IdealSheafData.IsLocallyPrincipal` from
`WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible`.
These are existing notions, not missing notions requiring new nodes.

The source theorem `Hom.isLocallyPrincipal_zeroLocus` (ZeroLocus.lean 570–576)
was read together with its surrounding section binders (line 481). It assumes
`SheafOfModules.IsInvertible.{u,u,u}` for M and N, not the node's recorded
`Scheme.Modules.IsInvertible`. Consequently its signature cannot be recorded
as this node's statement. The conversion in ProjectionFormula.lean 119–128 is
an ordinary lemma, not a global instance. The new statement preserves the
node's hypotheses. Its docstring reproduces all three proof steps and names
the bridge, common affine trivialization, and affine ideal lemmas and DAG nodes.
No dependency record is unusable: the invertible-module record is the exact
notion needed in the new binders.

Edge cases checked before writing:
- Empty scheme: the locally-principal predicate quantifies over points, so it
  is vacuous; no nonempty-scheme assumption is imposed.
- Zero morphism: on each trivializing affine its coefficient is zero, giving
  the principal ideal (0) and the whole scheme as zero locus.
- An isomorphism: coefficients are units, giving principal unit ideals and
  the empty zero scheme. Local principality does not require a non-zero-divisor.
- Nonreduced schemes and zero-divisor coefficients are allowed; no effective
  Cartier, regularity, field, characteristic, Noetherian, or separation
  hypothesis has been added. Arbitrary universe u matches the source category.

Searches for existing statements and name collisions:
- `msearch.py leanfinder`, query “zero locus of a morphism of invertible modules
  is locally principal”: eight Mathlib hits, chiefly Tilde and IdealSheafData
  results; none states this theorem.
- `msearch.py loogle`, query
  `AlgebraicGeometry.Scheme.Modules.Hom.isLocallyPrincipal_zeroLocus`:
  zero hits; unknown identifier in Loogle's Mathlib index.
- `msearch.py grep`, query
  `isLocallyPrincipal_zeroLocus|zeroLocus.*IsLocallyPrincipal`, restricted to
  AlgebraicGeometry: zero Mathlib hits.
- `msearch.py leansearch`, same natural-language query: unavailable,
  Internal Server Error; recorded as unavailable, with no mathematical verdict.
- `rg` over source WeilConjectures, project `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for `isLocallyPrincipal_zeroLocus` and the node
  id: finds the source theorem and its uses, but no theorem with the node's
  module-level invertibility binders. The source declaration's implicit
  SheafOfModules hypotheses are confirmed by reading the enclosing section.
- `rg` over Mathlib, source, project `lean/Sheaf`, and upstream names for
  `isLocallyPrincipal_zeroLocus_of_isInvertible`: no hits.
- `rg` for `def IsLocallyPrincipal|class IsLocallyPrincipal` finds the existing
  ideal-sheaf predicate; its definition and docstring were read.

Server verification: `scompile.py E1 lem-pc-zero-scheme-locally-principal`
compiled the module successfully in 1.6 seconds, with no errors or warnings.
No statement dispute, correction, new definition node, or dependency module.

## Second reading by E1

I independently read the item's JSON and ZeroLocusLocallyPrincipal.lean against
its actual source, ZeroLocus.lean 570–576. This node cites Lean source, not a
Stacks tag; I read the module header, the scheme/module binders at line 86,
and the Properties section's two SheafOfModules.IsInvertible binders at line
481. There is no ambient field, Noetherian, separation or regularity assumption.

The complete object/hypothesis/conclusion checklist is:

| Node item | Lean rendering | Verdict |
| --- | --- | --- |
| An arbitrary scheme X | `{X : Scheme.{u}}`, explicitly bound `universe u` | Exact; Scheme's local_affine field is the usual scheme condition. |
| Two O_X-modules M and N | `{M N : X.Modules}` | Exact; Mathlib Modules.Sheaf defines this as sheaves of modules over X.ringCatSheaf. |
| M invertible | `[M.IsInvertible]` | Exact dependency declaration, locally isomorphic to the structure sheaf. |
| N invertible | `[N.IsInvertible]` | Same exact predicate, independently imposed on N. |
| An O_X-linear morphism from M to N | `(φ : M ⟶ N)` | Exact; the category's Hom is SheafOfModules.Hom, not a map of global sections. |
| Its zero locus | `φ.zeroLocus` | Existing Hom.zeroLocus ideal-sheaf construction; the source's local ideal theorem identifies its affine equations with those of the zero scheme. |
| The entire zero locus is locally principal | `φ.zeroLocus.IsLocallyPrincipal` | Exact; the existing predicate quantifies over every x, then an affine neighbourhood U, then principality of its ideal. |

I opened the recorded dependency declarations themselves: Mathlib Scheme.lean
35–78 (Scheme and Scheme.Hom), and Modules/Invertible.lean 55–60
(Scheme.Modules.IsInvertible and its exists_isoUnit field). The latter's local
rank-one triviality implies quasi-coherence; a separate quasi-coherence binder
would add a redundant presentation requirement, so none is needed. I also read
Mathlib Modules/Sheaf.lean 37–48 (Modules and its morphisms), ZeroLocus.lean
151–179 (zeroLocusIdeal and zeroLocus), and IdealSheaf/Invertible.lean 131–135
(IsLocallyPrincipal). The conclusion concerns the scheme-theoretic ideal, not
just its support or radical. All notions are reused; no private definition.

The upstream Hom.isLocallyPrincipal_zeroLocus is not the node's exact Lean
signature: its enclosing section requires SheafOfModules.IsInvertible for both
modules. ProjectionFormula.lean 109–128 gives both comparison lemmas, including
IsInvertible.sheafOfModules_isInvertible as a lemma rather than a global instance.
Thus recording the upstream theorem verbatim would fail to use the dependency's
recorded notion. The delivered wrapper retains precisely the node's hypotheses.
I checked the natural-language proof against all three JSON steps: comparison
for both modules; common affine trivialization and the coefficient of φ(eM) in
the eN generator; the equality with Ideal.span {b}, giving local principality.
The docstring supplies all steps and their DAG node names.

Edge cases: the empty scheme makes the conclusion's point quantifier vacuous
and is not excluded. The zero morphism gives the principal zero ideal and the
whole zero scheme. An isomorphism gives unit ideals and the empty zero scheme.
Zero divisors and nilpotents are permitted because IsPrincipal does not impose
IsRegularPrincipal. A zero module is not invertible on a nonempty scheme, as
required, while the empty scheme permits it. There is no indexed family or
integer n to restrict (empty index sets and n = 0 are inapplicable). Arbitrary
characteristic and arbitrary universe u are allowed; X.Modules uses the same
universe as the source and admits invertible sheaves locally of rank one.

Independent searches used different language from the first worker:
- LeanFinder: “An O-linear map between line bundles has a locally principal
  vanishing ideal”; eight hits, chiefly ModuleCat.Tilde and a basic-open
  vanishing lemma, none the requested statement.
- Loogle: `Ideal.IsPrincipal`; zero hits, unknown identifier in its index.
- LeanSearch: “Locally principal ideal of vanishing of a homomorphism of line
  bundles”; service unavailable (Internal Server Error), no mathematical verdict.
- msearch grep: `IsLocallyPrincipal|line.bundle.*principal`; zero Mathlib hits.
- Direct rg over Mathlib, source WeilConjectures, project lean/Sheaf and upstream
  names for locally principal/vanishing/zero-locus terminology found the source
  theorem and its applications, but no statement with module-level invertibility
  binders. The existing predicate and zero-locus construction were opened, not
  inferred from names. The DAG already carries Hom.zeroLocus in
  def-pc-zero-scheme; no missing definition or dependency module was found.

No mathematical mismatch, node correction, hollow definition, proved theorem,
unbound variable or convention fault was found. I left the correct Lean and
node unchanged and appended this independent review only. The node's
lean.statement is verbatim the declaration's three-line signature. The only
proof is the required sorry. A fresh server single-file compile completed in
1.7 seconds with no errors or warnings.
