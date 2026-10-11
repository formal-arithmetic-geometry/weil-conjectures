## Worker report

The module `Sheaf.AlgebraicGeometry.BoundsFiberDegreesComp` states the product bound as
`AlgebraicGeometry.Scheme.Hom.boundsFiberDegrees_comp` and its final existential consequence as
`AlgebraicGeometry.Scheme.Hom.hasUniversallyBoundedFibers_comp`. Both proofs are `sorry`, as
required for stage 2. There are no new definitions, no dependency replacements, and no changes
to the node outside `lean`. Each declaration has its own source/proof docstring; the main one
contains all seven proof steps and the non-elementary nodes they use.

Hypothesis and clause matching:

- Schemes X, Y, Z and morphisms f:X→Y, g:Y→Z are `{X Y Z : Scheme.{u}}`,
  `(f : X ⟶ Y)`, `(g : Y ⟶ Z)`. No finiteness, affineness, flatness, separation,
  finite-type or Noetherian assumption is placed on these schemes or morphisms.
- The nonnegative integer bounds are `(n m : ℕ)`. The dependency definition explicitly
  restricts its bounds to nonnegative integers, represented by naturals.
- The assumption that n bounds the fibre degrees of f is `(hf : BoundsFiberDegrees f n)`;
  the assumption that m bounds the fibre degrees of g is `(hg : BoundsFiberDegrees g m)`.
- The composite g∘f is `f ≫ g`, in Lean's composition order.
- The conclusion that nm bounds its fibre degrees is `BoundsFiberDegrees (f ≫ g) (n * m)`.
  Unfolding the dependency definition gives, for every `z : Z`, the conjunction
  `IsFinite ((f ≫ g).fiberToSpecResidueField z)` and
  `((f ≫ g).fiberToSpecResidueField z).finrankΓ ≤ n * m`. Thus this conclusion includes
  BOTH finiteness over κ(z) and the claimed dimension inequality, not just a cardinality bound.
  The morphism `fiberToSpecResidueField` is the second projection of the pullback with
  `Z.fromSpecResidueField z`, and `finrankΓ` is the dimension of global sections over κ(z),
  with the algebra structure induced by that projection.
- The final 'in particular' clause has a separate theorem, with hypotheses
  `HasUniversallyBoundedFibers f` and `HasUniversallyBoundedFibers g` and conclusion
  `HasUniversallyBoundedFibers (f ≫ g)`. Unfolding this definition is existence of a natural
  bound. The proof docstring specifies the witness n*m.

Dependency declarations read and used:

- `def-pc-scheme`: its Mathlib leaf record names `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom`, defined in `Mathlib.AlgebraicGeometry.Scheme`.
  Read their full declarations and docstrings (lines 36–47 and 73–76).
- `def-weil-pbc-fibre-degree-bound`: imported its recorded module
  `Sheaf.AlgebraicGeometry.FiberDegreeBound`. Read both full definitions and docstrings:
  `AlgebraicGeometry.Scheme.Hom.BoundsFiberDegrees` and
  `AlgebraicGeometry.Scheme.Hom.HasUniversallyBoundedFibers`.
- Read the degree implementation in upstream
  `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`: `Scheme.Hom.ΓAlgebra`
  is induced by `ΓSpecIso.inv ≫ h.appTop`; `Scheme.Hom.finrankΓ` uses this algebra structure
  in `Module.finrank`. Read the pullback projection in `Mathlib.AlgebraicGeometry.Fiber`.
  These come through the recorded dependency import; they are not privately reproduced.

Edge cases checked before writing:

- Empty Z: the universal conclusion is vacuous and no point is required.
- Empty Y or X: empty fibres are finite schemes of dimension zero; zero bounds are retained.
- n=0 or m=0: a finite scheme over a field with zero-dimensional global sections is empty;
  therefore the relevant fibres and composite fibres are empty, with product bound zero.
- n=m=1: agrees with one-point reduced fibres (and empty fibres) and their composites.
- Nonreduced fibres are included: degree is vector-space dimension, not number of points.
  Nilpotent maximal ideals are handled in the natural-language proof by nilpotent Nakayama.
- No restriction on characteristic or residue fields, and no connectedness/nonemptiness
  assumptions. Universe u is explicit and arbitrary; schemes may all be placed in any common
  universe. Every variable is explicitly bound.

Searches made using `/home/ubuntu/weil-launcher/msearch.py C1
lem-weil-pbc-composition-fibre-degree-bound` (recorded in `searches.jsonl`):

- LeanSearch, query 'Composition of scheme morphisms with fibre degrees bounded by n and m
  has fibre degrees bounded by n times m': service unavailable (Internal Server Error).
  This is an availability failure, not evidence of absence.
- LeanFinder, same query: eight hits, including `IsFinite.instCompScheme`,
  `IsFinite.instIsStableUnderCompositionScheme`, `IsFinite.comp_iff`,
  `locallyOfFiniteType_comp`, and stability of locally quasi-finite morphisms under composition.
  None gives the product bound on arbitrary finite scheme-theoretic fibres.
- Loogle, `AlgebraicGeometry.Scheme.Hom.finrank`: twelve hits in Morphisms.FlatRank,
  including `finrank_comp_left_of_isIso` and base-change rank equalities. These involve
  finite flat ranks, not the required arbitrary fibre degree bounds.
- Mathlib grep, regular expression
  `universally.?bounded|BoundsFiberDegrees|fiber.*degree.*comp|fibre.*degree.*comp`
  in AlgebraicGeometry: zero hits.
- Source/project rg for `FibreDegree|fibreDegree|BoundedFib|boundedFib|fibre-degree-bound|
  composition-fibre-degree-bound`: upstream hits concern Picard degrees, not this statement.
  Source/project/name-index rg for `boundsFiberDegrees_comp|hasUniversallyBoundedFibers_comp|
  BoundsFiberDegrees|HasUniversallyBoundedFibers`: only the landed dependency module matches;
  no prior theorem or name clash. Source grep for the exact item id returned no hit.

Source check: the local literature file `literature/stacks-project/morphisms.tex` is absent
on this machine, so I opened the authoritative [Stacks Tag 03J6](https://stacks.math.columbia.edu/tag/03J6).
Its product-bound statement agrees with the node. No correction or statement dispute is needed.

Validation: server compilation and delivery dry run are recorded below after they complete.
The second reading is left to the independent reader; nothing has been pushed.

Server compilation: clean, exit code 0, compiled in 1.8 seconds. The first delivery dry run
also passed its server compile and all module/node checks, but preflight observed an unrelated
concurrent working-tree change to `lem-weil-pbc-change-ideal-completion.json`, in addition to
the expected missing independent second reading. Retrying the prescribed dry run without
changing the unrelated file.

The retry printed `OK (dry run)` (commit `33a4cee5a`): the delivery compiles and passes the
preflight except for the independent second reading, which the second reader writes.
Nothing was pushed. The unrelated concurrent-change failure did not recur.

## Second reading by C1

Independent reading of the sandbox node and both declarations, against Stacks Tag 03J6.
I also read the raw Stacks `morphisms.tex`, lines 15287–15320 and 15368–15423,
obtained from https://raw.githubusercontent.com/stacks/stacks-project/master/morphisms.tex
in the sandbox as `morphisms-source.tex`. Section `section-universally-bounded` introduces
finite schemes over arbitrary fields and their degree; it assumes no global Noetherian,
finite-type, separated, flat, affine, or nonempty condition. The lemma introduces arbitrary
scheme morphisms. No statement correction is present or needed.

The complete object/hypothesis/conclusion list and matching verdicts are:

1. Schemes X, Y, Z: `{X Y Z : Scheme.{u}}`. Read `def-pc-scheme` and Mathlib's
   `Scheme` (locally ringed space locally isomorphic to spectra) and `Scheme.Hom`
   (locally ringed space morphism). These are exactly the node's objects. PASS.
2. Morphisms f:X→Y, g:Y→Z: `(f : X ⟶ Y) (g : Y ⟶ Z)` in both signatures.
   No extra instances or geometric hypotheses. PASS.
3. Bounds n and m: `(n m : ℕ)`. Read the dependency node
   `def-weil-pbc-fibre-degree-bound`: clause (1) explicitly specifies n≥0, so naturals
   render exactly the bounds used by this node. Stacks' bare wording 'integer' is
   interpreted through that reviewed dependency convention; negative bounds are not
   part of its notion, and are not silently excluded by this delivery. PASS.
4. n bounds the fibres of f: `(hf : BoundsFiberDegrees f n)`. Read the dependency's
   recorded module `Sheaf.AlgebraicGeometry.FiberDegreeBound`, not merely its name.
   Its definition is `∀ y : Y, IsFinite (f.fiberToSpecResidueField y) ∧
   (f.fiberToSpecResidueField y).finrankΓ ≤ n`. PASS.
5. m bounds the fibres of g: `(hg : BoundsFiberDegrees g m)`, with the identical
   interpretation at all points of Z. PASS.
6. Composite g∘f: `f ≫ g`, the category's forward composition order. PASS.
7. For each z∈Z, the composite fibre X×_Z Spec κ(z) is finite over κ(z): the
   first conjunct of `BoundsFiberDegrees (f ≫ g) (n * m)`. Opened Mathlib
   `AlgebraicGeometry/Fiber.lean`: `fiber` is the pullback with `fromSpecResidueField`,
   and `fiberToSpecResidueField` is precisely `pullback.snd`. Thus finiteness is
   finiteness of the structure morphism, not finiteness of the set of points. PASS.
8. Its degree is at most nm: the second conjunct of that same conclusion. Opened
   upstream `Morphisms/FiberDegree.lean`: `ΓAlgebra` is induced by
   `ΓSpecIso.inv ≫ h.appTop`; `finrankΓ` is `Module.finrank` of global sections with
   that algebra structure. It is the required vector-space dimension, including
   nilpotents and residue-field extension degrees. Finiteness is asserted alongside
   the bound, so the infinite-dimensional fallback of `finrank` does not weaken it.
   Both universal conclusions are under the same quantifier `∀ z`. PASS.
9. In particular universally bounded fibres compose:
   `hasUniversallyBoundedFibers_comp` takes
   `(hf : HasUniversallyBoundedFibers f) (hg : HasUniversallyBoundedFibers g)` and
   concludes `HasUniversallyBoundedFibers (f ≫ g)`. The recorded dependency is
   `∃ n : ℕ, BoundsFiberDegrees f n`; the docstring chooses n,m then n*m.
   This separate statement covers the whole final clause, with no extra hypothesis. PASS.

Edge cases: empty Z makes the fibre quantifier vacuous; empty X or Y is allowed,
with empty fibres and degree zero. For n=0, every fibre of f has zero-dimensional
finite global-section algebra and is empty, hence X is empty. For m=0, Y is empty
and the morphism from X forces X empty. The composite degree bound is zero in both
cases. Empty products in the docstring's finite-local-factor argument are allowed.
No separate indexing set or zero-object binder occurs. Arbitrary nonreduced fibres,
all residue fields and all characteristics are included. The explicit arbitrary
universe u is the standard common universe for the category of schemes and its
pullbacks; there is no smallness, field, or nonemptiness binder. All variables and
universes in both signatures are bound.

Independent H4 searches (queries differ from the worker's):

- LeanFinder via msearch: `dimension of global sections of composite scheme fibre
  bounded by product without flatness`: eight hits, chiefly Flat, its pullback
  instances, and Module.rankAtStalk product/tensor/base-change results. None states
  this product bound for arbitrary scheme morphisms.
- Loogle via msearch: `"finrankΓ"`: zero hits (the source-only notion is not indexed).
- LeanSearch via msearch: `finite scheme theoretic fibres dimension bound product
  under composition`: Internal Server Error, recorded as unavailable, not absence.
- Direct rg in all upstream WeilConjectures, Mathlib/AlgebraicGeometry and project
  lean/Sheaf for `bounded.*(fiber|fibre)|(fiber|fibre).*bounded|finrankΓ.*comp|
  comp.*finrankΓ|fiberDegree.*comp|comp.*fiberDegree`. Only the existing dependency,
  special étale degree bounds, open restrictions, isomorphism invariance and Cartier
  divisor formulas were relevant hits. Opened `fiberDegree_comp_ι` and
  `fiberDegree_comp_left_of_isIso`: they assert restriction/isomorphism comparisons
  and require affine morphisms, not this general composition bound.
- Direct name-clash rg for both new full-name suffixes in the upstream name index,
  all Mathlib, upstream WeilConjectures and project lean/Sheaf: no hit.

No existing exact statement was found. The module uses the dependency's public
notions, with no private copy. There are no new definition nodes or dependency
modules to audit under H12/H13. There is no hollow definition: this module contains
only the two named theorems, each with `by sorry`. The module and both declaration
docstrings identify Tag 03J6 and the exact blueprint id. I matched the main
docstring's seven numbered steps to all seven node proof steps: finite Y_z and its
local factors; pasting and field-point fibres; affine X_z; quotient fibres;
decomposition of A; nilpotent Nakayama; summation and finiteness. The second
statement's docstring carries the existential consequence of step 7. Header,
namespace, sole used import and line widths follow the conventions.

Mismatches found: none. Changes: appended this independent review only; preserved
the correct Lean and node. The node's `lean.statement` is verbatim the main
signature, excluding `:=`, and `lean.declarations` includes the final consequence.

Independent validation: prescribed `scompile.py` with the absolute sandbox module
path compiled cleanly on the server in 1.7 seconds, exit code 0, no warnings.
