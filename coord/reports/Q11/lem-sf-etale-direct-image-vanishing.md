## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleDirectImageVanishing` states
`AlgebraicGeometry.etale_direct_image_vanishing_above_twice_dimension`, with its
entire proof `by sorry`. It introduces no definitions. The node copy changes only
`lean`; there are no new nodes, dependency repairs, or statement corrections.

The conclusion uses the existing definition
`AlgebraicGeometry.Etale.HasUniformDirectImageVanishingLE A f (2 * d)`. Its body is
exactly

```lean
∀ (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) (q : ℤ),
  ((2 * d : ℕ) : ℤ) < q → IsZero (Etale.higherDirectImage A f q M)
```

The cast of the natural product is the integer product in the node. Thus this
single conclusion renders both the primary all-module higher-direct-image
vanishing and its stated UDV interpretation, without adding a duplicate conjunct.
The UDV predicate's actual source has no finite-field or separatedness parameters;
its node records the arithmetic setting in which that predicate is used. In that
setting this conclusion specializes to the coefficient-stage ring and separated
morphism specified there.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node text | Lean |
| --- | --- |
| Algebraically closed field `k` | `{k : Type u} [Field k] [IsAlgClosed k]` |
| `d ∈ ℕ` | `(d : ℕ)` |
| Schemes `X,Y` | `{X Y : Scheme.{u}}` |
| Finite-type `k`-structure on `X` | `(aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]` |
| Finite-type `k`-structure on `Y` | `(aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY]` |
| `dim X ≤ d` | `(hX : topologicalKrullDim X ≤ (d : WithBot ℕ∞))` |
| Finite-type morphism `f : X → Y` | `(f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f]` |
| Finite commutative coefficient ring | `(A : Type (u + 1)) [CommRing A] [Finite A]` |
| Annihilated by an integer invertible in `k` | `hA : ∃ n : ℕ, 0 < n ∧ IsUnit (n : k) ∧ ∀ a : A, n • a = 0` |
| Small étale sites | `X.smallEtaleTopology`, `Y.smallEtaleTopology` in the existing predicate and higher-direct-image definition |
| Every sheaf of `A`-modules | `∀ M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)` in the predicate |
| Every `q > 2d` | `∀ q : ℤ, ((2 * d : ℕ) : ℤ) < q → ...` in the predicate |
| `R^q f_* M = 0` as a module sheaf | `IsZero (Etale.higherDirectImage A f q M)` |
| Separatedness is unnecessary | No `IsSeparated f` binder |
| Global finite-field/coefficient-stage UDV interpretation | The conclusion already is the recorded UDV predicate, applicable in that setting |
| Dimension is topological Krull dimension | The recorded `topologicalKrullDim`; the codomain `WithBot ℕ∞` includes the empty scheme |
| Finite type has the recorded meaning | Both `LocallyOfFiniteType` and `QuasiCompact` are explicitly bound on all three specified structure/morphism maps |

Writing the annihilator as a positive natural number is equivalent to writing an
integer invertible in a field: it is nonzero, and its absolute value has the same
annihilation and invertibility properties. Equivalently one can check annihilation
on `1_A`; multiplication then gives annihilation of every `a`. This formulation
does not impose `Nontrivial A`.

There is deliberately no compatibility hypothesis `f ≫ aY = aX`: the node's proof
explicitly allows replacing the initial `k`-structure on `X` by `f ≫ aY`. The draft
was checked for this issue and the extra binder was removed before recording the
signature. The supplied finite-type hypotheses on the initial map `aX` remain, as
the node requests. No `f.IsOver` instance is imposed.

The coefficient universe follows the dependency's six-functor encoding:
`A : Type (u + 1)`, module objects in `ModuleCat.{u + 1} A`, and schemes in
`Scheme.{u}`. This is the encoding explicitly authorized by the note of
`def-weil-pbc-etale-sheaves`; no private module-sheaf model or arbitrary replacement
of the direct-image functor is used.

Dependency declarations inspected and used:

- `Mathlib.AlgebraicGeometry.Sites.Etale`:
  `AlgebraicGeometry.Scheme.smallEtaleTopology`, with
  `AlgebraicGeometry.Scheme.Etale` in
  `Mathlib.AlgebraicGeometry.Morphisms.Etale` (objects and topology, finite limits).
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`; and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`:
  `AlgebraicGeometry.QuasiCompact` (the recorded conjunction for finite type).
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.lowerStar`, objectwise base-change pushforward.
- `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs`:
  `AlgebraicGeometry.Etale.higherDirectImage`, defined as degree-`q` homology of
  the right-derived module pushforward of the degree-zero module sheaf.
- `WeilConjectures.AlgebraicGeometry.EtaleSheaves` and the recorded note for
  `def-weil-pbc-etale-sheaves`: the category used here is the existing
  `CategoryTheory.Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)` encoding, not
  the distinct set-valued locally constant predicates in that module.
- `WeilConjectures.SixFunctors.Etale.Derived.DirectImageVanishing`:
  `AlgebraicGeometry.Etale.HasUniformDirectImageVanishingLE`; the entire current
  module was read using `scompile.py --source`, because the older source checkout
  lacks it. Its current copy is also in the shared read-only library.
- Proof-only `Mathlib.FieldTheory.IsSepClosed`: `IsSepClosed` and the instance
  `IsSepClosed.of_isAlgClosed`.
- Proof-only
  `WeilConjectures.SixFunctors.Etale.Derived.DirectImageVanishingTorsion`:
  `AlgebraicGeometry.Etale.isZero_higherDirectImage_of_two_mul_lt`, the recorded
  declaration of `lem-kun-relative-torsion-direct-image-dimension-bound`.

The docstring gives all three proof steps of the DAG node: derive separable
closedness/torsion and use the induced `k`-structure, specialize the relative
torsion direct-image dimension bound, and read its all-module conclusion as UDV.
Statement-dependency imports are public; the two imports needed only for the proof
plan are ordinary imports. No proof has been attempted.

Edge cases checked:

- Empty `X`: `topologicalKrullDim X = ⊥` fits the bound, and no nonemptiness
  hypothesis has been introduced.
- `d = 0`: the conclusion covers all integer degrees `q > 0`, with no assertion
  about degree zero or any omitted positivity case.
- Zero coefficient ring: allowed by `CommRing A` without `Nontrivial A`; `n = 1`
  is a valid annihilator invertible in every field. All zero-ring module sheaves
  are included.
- Positive characteristic: the hypothesis is precisely invertibility of the
  annihilating integer; no characteristic-zero or prime-order restriction appears.
- Nonseparated `f` and unrelated initial `k`-structures: allowed, as stipulated.
- Every module sheaf is included; no finiteness, constructibility, lisse or stalk
  condition is imposed on `M`.
- Negative and zero cohomological degrees are not spuriously forced to vanish:
  `2 * d` is nonnegative and only larger integer degrees occur.

Searches (2026-10-16):

- `msearch.py ... leanfinder` with query
  `higher direct image sheaf etale vanishing twice Krull dimension finite type algebraically closed field`:
  eight hits, concerning étale loci, formal étaleness and the étale composition
  property; none states this higher-direct-image bound.
- `msearch.py ... loogle` with query
  `AlgebraicGeometry.Etale.higherDirectImage, IsZero`: zero hits, unknown upstream
  identifier `AlgebraicGeometry.Etale.higherDirectImage` in the Mathlib service.
- `msearch.py ... grep` with query
  `higherDirectImage|HasUniformDirectImageVanishingLE|two_mul.*[dD]im` in
  `Mathlib/AlgebraicGeometry`: zero hits.
- `msearch.py ... leansearch` with query
  `Higher etale direct images of finite coefficient module sheaves vanish above twice the Krull dimension over an algebraically closed field.`:
  unavailable, service returned `Internal Server Error`; no search verdict claimed.
- `rg` on the older `WeilConjectures` tree for the item id and the higher-direct-image
  names found the existing canonical higher-direct-image definition and surrounding
  base-change material, but no declaration for this exact statement. The older
  checkout has no `Derived/DirectImageVanishing.lean`.
- `rg` on the shared `lean/WeilConjectures` found the published
  `Etale.hasUniformDirectImageVanishingLE_two_mul` and the torsion relative bound;
  their full signatures/docstrings were read. Both are stronger than this node:
  separably closed replaces algebraically closed, there is no invertible-annihilator
  requirement, and the source/target finite-type hypotheses are weaker. Their
  compatibility equation is handled here by using `aX := f ≫ aY`, as in the DAG
  proof. Consequently they are proof inputs, not an existing signature with exactly
  this node's hypotheses. No notion is redefined.
- `rg` on `lean/Sheaf` for the item id, the proposed name, and the upstream bound
  names found no copy of this exact specialized statement; the relative torsion
  bound appears as an input to `ProperUnboundedBaseChangeModN`.
- `tools/lean_names_upstream.py show` read the stored index (blueprint 633 nodes,
  docstring 904 nodes); focused `rg` on `dag/lean_names_upstream.json` found no
  item-id or proposed-name entry. The new full declaration name was also searched
  in Mathlib/upstream/project sources before use.

Source availability: the node, its complete proof plan, the dependency nodes and
the relevant canonical Lean declarations were read. The cited blueprint Markdown
is not installed in this read-only checkout; its archived raw URL returned 404.
No source-based statement correction was needed or made.

Validation: the final module compiles without errors or warnings using the required
`scompile.py Q11 lem-sf-etale-direct-image-vanishing ...` wrapper, both as the
sandbox file and as its final library module path. There is one named theorem
with the required `sorry` proof, with all variables and universes explicitly bound.
The worker leaves the independent second reading to the second reader.

## Second reading by Q11

I opened the copied node and the final module and matched the statement item by item.

* The node's algebraically closed field `k` is rendered by `{k : Type u}` with
  `[Field k] [IsAlgClosed k]`; no separable-closed or characteristic-zero assumption
  is added.
* The finite commutative coefficient ring is `(A : Type (u + 1))` with
  `[CommRing A] [Finite A]`.  The hypothesis `hA` supplies a positive natural
  integer whose image in `k` is a unit and which annihilates every element of `A`,
  exactly the node's torsion/invertibility condition.  It permits the zero ring.
* The objects `X` and `Y` are `{X Y : Scheme.{u}}`, with explicit structure maps
  `aX : X ⟶ Spec (.of k)` and `aY : Y ⟶ Spec (.of k)`, each carrying
  `[LocallyOfFiniteType]` and `[QuasiCompact]`.  These are precisely the recorded
  finite-type `k`-scheme conditions; no compatibility `aX = f ≫ aY` is imposed,
  as the node's proof explicitly permits replacing the supplied `X` structure.
* The morphism `(f : X ⟶ Y)` has `[LocallyOfFiniteType f]` and
  `[QuasiCompact f]`, rendering finite type.  There is no `IsSeparated f` or
  properness hypothesis.
* The dimension clause is `(d : ℕ)` and
  `hX : topologicalKrullDim X ≤ (d : WithBot ℕ∞)`, using Mathlib's topological
  Krull dimension, including the empty scheme case.
* The conclusion is exactly
  `Etale.HasUniformDirectImageVanishingLE A f (2 * d)`.  Its existing definition
  expands to every `M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)` and every
  integer `q`, with `((2 * d : ℕ) : ℤ) < q` implying
  `IsZero (Etale.higherDirectImage A f q M)`.  Thus it renders the node's
  higher-direct-image clause and its UDV interpretation without an extra conjunct.

The small étale sites and the module-sheaf category are the exact recorded
declarations `Scheme.smallEtaleTopology` and
`Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)`; the higher direct image is the
canonical `Etale.higherDirectImage` used by the existing UDV predicate.  The
coefficient universe is one above the scheme universe, as required by that
encoding.  The empty scheme, `d = 0`, zero coefficient ring, positive
characteristic, negative/zero degrees, and non-separated `f` are all covered by
the signature; no case is silently excluded.  In particular, only degrees
strictly above `2*d` are asserted, so degree zero is not forced to vanish when
`d = 0`.

The initial signature introduced `A` before `d`, the schemes and `f`. I reordered
the binders to follow the node: `k`, `d`, `X,Y` and their structure maps and
dimension hypothesis, `f`, then `A` and its annihilator. This is the sole Lean
change; no hypothesis, conclusion, or DAG statement changed. The explicit pair
of finite-type structure maps is not a mismatch; these are the data required to express finite-type `k`-schemes in Lean and
do not constrain the theorem's conclusion.  I also confirmed that `hA` does not
add `Nontrivial A` and that no `f.IsOver` equality is hidden in the binders.

I independently repeated the searches using different wording:

* LeanFinder: `Bounded cohomological dimension of pushforward of torsion sheaves
  on the small etale site of a finite dimensional scheme` returned eight hits
  about derived t-structures, etale loci and the abelian category of scheme
  modules. None states this bound.
* Loogle: `"higherDirectImage"` returned zero hits.
* LeanSearch: `Pushforward of torsion etale module sheaves has higher derived
  functors zero in degrees above twice the dimension over a closed field.` was
  unavailable (Internal Server Error); no verdict is claimed for that service.
* `rg` over Mathlib/AlgebraicGeometry, the slopmaster2 WeilConjectures tree,
  `lean/Sheaf`, and the current published Derived modules searched
  `cohomologicalDimension`, `higherDirectImage`, the proposed declaration name
  and `HasUniformDirectImageVanishingLE`. It found the canonical definitions
  and the stronger existing relative bounds, not an exact duplicate signature.
  I read `Etale.hasUniformDirectImageVanishingLE_two_mul` in full via the required
  `scompile.py --source` command: it assumes separable closedness, omits the
  annihilator and finiteness of the structure maps, and therefore serves as a
  stronger proof input rather than this exact statement.

I read all six statement-dependency node records and their relevant definitions:
`Etale.lowerStar` is objectwise base-change pushforward, `Etale.higherDirectImage`
is homology of its bounded-below derived functor on a degree-zero module sheaf,
`Scheme.smallEtaleTopology` is the canonical small site, the module-valued sheaf
encoding is expressly authorized in `def-weil-pbc-etale-sheaves`, and
`topologicalKrullDim` and the two finite-type classes are Mathlib's definitions.
The UDV definition was opened in the current server source, not inferred from
its name. No new node or dependency module is needed; none is delivered.

The original blueprint Markdown was absent locally, but I retrieved and read it
read-only from `/home/ubuntu/weil-newtargets/literature/blueprint/master/blueprint/`
on the server. It has the algebraically closed field, finite-type schemes and
morphism, finite coefficient ring with invertible annihilator, all module
sheaves, the `q > 2d` bound, and no separatedness. The already reviewed stage-1
node makes commutativity and `d ∈ ℕ` explicit and correctly scopes the UDV
interpretation. Its corrected proof avoids the original blueprint's incorrect
objectwise higher-direct-image evaluation. I also read Stacks `morphisms.tex`,
`section-finite-type`, `definition-finite-type` (01T0/01T1) and the following
characterization: finite type is exactly locally finite type plus quasi-compact.
There is no extra ambient separatedness or Noetherian hypothesis there.

The module and theorem docstrings carry the required source and blueprint id;
the theorem's docstring covers all three node proof steps in order. The only
proof is `by sorry`, and there is no new definition or hollow data. The node's
`lean.statement` was synchronized verbatim with the reordered signature. The
required `scompile.py` wrapper compiled this final module both as a sandbox and
at its final library path without errors or warnings. No variable or universe
is left unbound.
