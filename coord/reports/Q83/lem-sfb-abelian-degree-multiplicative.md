## Worker report

The module `Sheaf.AlgebraicGeometry.AbelianVariety.EndomorphismDegreeMultiplicative`
defines the degree d introduced in the item and states both its normalization and
multiplicativity. The theorem has exactly one `sorry`; the definition has real data.
No node statement or dependency list is changed.

Hypotheses and clauses, matched individually:

- The field k is `{k : Type u} [Field k]`, with an explicitly declared universe u.
- Algebraic closure of k is `[IsAlgClosed k]`; no characteristic restriction occurs.
- A/k is `(A : Over (Spec (.of k)))`.
- The group-scheme structure is `[GrpObj A]` and the abelian-variety condition is
  `[IsAbelianVariety A]`, which says proper, smooth and connected over k.
- Positive dimension is `(hpos : 0 < IsAbelianVariety.dim A)`.
- The endomorphisms are `a b : A ⟶ A` with `[IsMonHom a] [IsMonHom b]`.
  These are group homomorphisms, rather than arbitrary scheme self-maps.
- The node's d(a) is `abelianEndomorphismDegree a`, defined by
  `if IsIsogeny a then isogenyDegree a else 0`. The existing `isogenyDegree`
  is `(GrpObj.ker a).hom.finrankΓ`, the k-dimension of the actual kernel algebra.
  This helper belongs to the item's own definition of d; it is not an independent
  new notion, and is listed in `lean.declarations` with the item's blueprint id.
- The first conjunct is `abelianEndomorphismDegree (𝟙 A) = 1`.
- The second conjunct quantifies over every pair of group endomorphisms and says
  `abelianEndomorphismDegree (b ≫ a) =
   abelianEndomorphismDegree a * abelianEndomorphismDegree b`.
  Categorical composition `b ≫ a` is the node's a ∘ b, with the required factor order.
- No separability assumption is added. The kernel algebra may be nonreduced, so its
  vector-space dimension retains the inseparable contribution to its order.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field` (commutative ring and division ring).
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed` (every polynomial splits,
  equivalently every nonconstant polynomial has a root).
- `WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs`:
  `AlgebraicGeometry.IsAbelianVariety` and `AlgebraicGeometry.IsAbelianVariety.dim`.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj`, together with
  `CategoryTheory.IsMonHom` from its monoid interface. These are the recorded
  group-scheme and group-homomorphism notions, instantiated in `Over (Spec k)`.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`:
  `AlgebraicGeometry.IsIsogeny` and `AlgebraicGeometry.isogenyDegree`.
  `IsIsogeny` includes homomorphism, surjectivity, and finite scheme kernel.
- The latter's canonical kernel is `CategoryTheory.GrpObj.ker` from
  `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp`;
  its order is `AlgebraicGeometry.Scheme.Hom.finrankΓ` from
  `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`.

Statement dependencies are public imports (including their public transitive imports).
The recorded proof module `WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny`
is a plain import. It supplies `IsIsogeny.isFinite`, `IsIsogeny.flat`,
`IsIsogeny.finrank_eq`, and `IsIsogeny.isFiniteLocallyFreeOfDegree`.
The recorded finite-locally-free definitions are already public dependencies of that
module and of GroupScheme.Defs. The three proof-only nodes
`lem-sfb-equal-dimension-isogeny-criterion`,
`lem-sfb-finite-kernel-equal-dimension-isogeny`, and
`lem-sfb-finite-locally-free-degree-composition` have no recorded modules in the read
clone; they are named in the proof docstring and no speculative import is introduced.
No missing statement interface or dependency repair was necessary.

Source checked directly: Milne AV PDF pages 38 and 52–53, corresponding to printed
pages 32 and 46–47. Proposition 7.1 gives the equal-dimension criteria and the following
paragraph identifies degree with finite-flat rank. Printed p.46 explicitly extends
degree by zero to all endomorphisms; Remark 10.11 uses its multiplicativity.
The complete four-step DAG proof is rendered in the theorem docstring, including
reflection of isogenies from a composite, multiplication of finite locally free
ranks, and the nonisogeny cases. Nothing is proved in stage 2.

Edge cases checked before writing:

- Identity: its kernel is Spec k with coordinate-algebra dimension one.
- A zero group endomorphism of positive-dimensional A is not an isogeny and has
  degree zero, as do its composites. More generally either nonisogeny factor forces
  a nonisogeny composite by the two equal-dimension criteria in the DAG proof.
- Isogenies with nonreduced kernels in positive characteristic remain covered;
  the definition never counts geometric points.
- A product abelian variety can have nonzero nonisogeny projections. Their finite
  kernel condition fails, so the conditional correctly returns zero even if their
  global-function kernel dimension is nonzero. Using isogenyDegree alone would
  therefore be incorrect.
- Dimension zero is excluded precisely by the node's positive-dimension hypothesis;
  no extra nonemptiness or commutativity hypothesis is imposed.
- The arbitrary universe u covers all field and scheme sizes in the recorded API.

Searches for existing declarations (all run 2026-10-24):

- msearch LeanFinder: "Degree extended by zero for nonisogenies is multiplicative on
  endomorphisms of an abelian variety". Eight elliptic division-polynomial and
  variable-change hits; none states this theorem or defines its degree function.
- msearch Loogle: `"isogenyDegree"`. Zero hits.
- msearch grep: `isogeny|isogenyDegree` in Mathlib/AlgebraicGeometry. Zero hits.
- msearch LeanSearch: "The degree of endomorphisms of an abelian variety extended by
  zero on nonisogenies is multiplicative". Eight hits, including AddMonoid.End,
  multiplicativity of morphism properties, and rational-function degree; no match.
- rg over lean/WeilConjectures and lean/Sheaf:
  `isogenyDegree|if .*IsIsogeny|if .*isIsogeny`. Only the upstream group-scheme
  definition and abelian-variety Isogeny/Final modules use isogenyDegree. They do
  not define the zero extension or state the requested composition theorem.
- rg for the exact item id over lean/WeilConjectures: no hits.
- rg for both proposed declaration names over Mathlib, WeilConjectures, Sheaf, and
  dag/lean_names_upstream.json: no collisions.
- DAG definition-node search for isogeny and degree: only def-sc-isogeny and
  sk-def-av-isogeny, which define isogeny degree, not the zero extension.
  blueprint_refs.py search "isogeny" returned seven blueprint nodes about isogenies,
  none defining the zero extension or stating this multiplicativity theorem.

No STATEMENT-DISPUTED or statement correction.

## Second reading by Q83

A second pass in this worker session compared the full node statement with the
finished file and read the upstream definitions again. In particular it checked
that nonisogenies are explicitly assigned zero (the upstream kernel-order function
alone would not suffice), that b ≫ a means a ∘ b, that both factors are homomorphisms,
that positivity is retained, and that the identity clause and inseparable kernels
are included. No mismatch remained and no node correction was needed. This is a
self-check, not a claim of an independent second agent; the dispatcher forbids
starting other agents and the maintainer supplies the independent review.

Validation: scompile.py compiled both the sandbox and actual library module cleanly
on the server (exit 0). deliver2.py --no-push reported OK: commit 034edce287d
passes preflight and compiles; nothing pushed. All Lean lines are at most 100
characters. The node differs only in its lean field, and autoImplicit is disabled.
