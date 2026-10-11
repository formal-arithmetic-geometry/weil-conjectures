## Worker report

The module `Sheaf.AlgebraicGeometry.CoherentPropertyIrreducible` states
`AlgebraicGeometry.Scheme.Modules.coherent_property_irreducible`, with `sorry` as its only
proof. It defines no notion and proves nothing. Its statement agrees with Stacks Project,
Cohomology of Schemes, Lemma 30.12.5, [Tag 01YH](https://stacks.math.columbia.edu/tag/01YH),
label `lemma-property-irreducible`. The local literature checkout does not contain
`literature/stacks-project/coherent.tex`, so the source statement and proof were read at
that official tag page.

Clause-by-clause correspondence:

- Scheme: `(X : Scheme.{u})` is Mathlib's scheme, not a different ringed-space category.
- Noetherian: `[IsLocallyNoetherian X] [CompactSpace X]` are exactly local Noetherianity
  and quasi-compactness of the underlying space. Mathlib's `IsNoetherian` packages these
  same two conditions. Neither separatedness nor an affine hypothesis is imposed.
- Closed irreducible subset: `(T : Set X)`, `hTclosed : IsClosed T`, and
  `hTirreducible : IsIrreducible T` include the nonemptiness required for irreducibility.
- Generic point: `(ξ : X)` and `hξ : IsGenericPoint ξ T`, i.e. the closure of `{ξ}` is T.
- Property of coherent modules supported in T: `(P : X.Modules → Prop)` permits an
  arbitrary predicate, and all its occurrences under (1), (3), and the conclusion are
  restricted by coherence and support assumptions. Extending the property arbitrarily
  to the other objects introduces no assumption about them.
- Condition (1): `hshort` quantifies over every `S : ShortComplex X.Modules` and assumes
  `S.ShortExact`. Its three coherence assumptions and three support-in-T inclusions
  restrict all three terms exactly as in the node. The conjunction of the three
  implications renders each of the three choices of two terms implying the third.
  Mathlib's `ShortExact` means exactness together with monic first map and epic second
  map, hence includes the two endpoint zeros.
- Condition (2), integral closed subschemes: `hsmaller` quantifies over every
  `(Z : Scheme.{u}) (i : Z ⟶ X)` with `IsClosedImmersion i` and `IsIntegral Z`.
  `Set.range i.base ⊂ T` says its image is a strict subset of T.
- Condition (2), every quasi-coherent ideal: `(I : Z.Modules)` with
  `(ι : I ⟶ SheafOfModules.unit Z.ringCatSheaf)`, `Mono ι`, and `I.IsQuasicoherent`
  is precisely a quasi-coherent submodule of the structure sheaf. An O_Z-submodule
  of O_Z is an ideal. This represents the ideal as an injectively included module;
  it does not restrict to nonzero, principal, invertible, or finite-rank ideals.
  Every quasi-coherent ideal gives such an inclusion, and each such inclusion is
  isomorphic to its image ideal. Isomorphism invariance of P on coherent supported
  modules follows from (1) and (3): the sequence G → G → 0 gives P(0), and an
  isomorphism F → F' fits into the short exact sequence F → F' → 0.
- Condition (2), pushforward: `P ((pushforward i).obj I)` is P(i_* I), the existing
  module pushforward with scalars restricted along the structure-sheaf map of i.
  On the Noetherian closed subscheme these ideals and their pushforwards are coherent;
  no extra coherence condition was added to the quantification.
- Condition (3), existence and coherence: `hG : ∃ G : X.Modules, ...` starts with
  `RingedSpace.IsCoherent X.toRingedSpace G`.
- Condition (3)(a): `{x : X | ¬ Subsingleton (G.presheaf.stalk x)} = T` says support
  equals T, using the prescribed inline nonzero-stalk locus.
- Condition (3)(b): `∀ a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk ξ), ∀ v, a • v = 0`
  says the ambient maximal ideal annihilates the stalk module.
- Condition (3)(c): the existential `inst : Module (X.residueField ξ) ...` supplies
  the quotient scalar action on this SAME stalk, and
  `∀ a v, a • v = (X.residue ξ) a • v` requires it to recover the original
  stalk-ring action. The residue map is surjective, so this compatibility makes the
  action unique; its existence follows from (b). `Module.finrank ... = 1` then
  renders the stated dimension one. For a field, finrank one excludes the
  infinite-dimensional case (which has finrank zero). This does not allow an
  unrelated vector-space structure or a different stalk.
- Condition (3)(d): the final conjunct `P G`.
- Conclusion: `∀ F : X.Modules, RingedSpace.IsCoherent X.toRingedSpace F →
  {x : X | ¬ Subsingleton (F.presheaf.stalk x)} ⊆ T → P F` is exactly the assertion
  about every coherent module supported inside T.

Dependencies read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme` and
  scheme morphisms. Full scheme signature read from the pinned Mathlib source.
- `pqf-def-locnoeth`: `Mathlib.AlgebraicGeometry.Noetherian`,
  `AlgebraicGeometry.IsLocallyNoetherian`; `CompactSpace X` gives the scheme
  quasi-compactness convention of `def-weil-pbc-scheme-conventions`, which has no
  declaration or notion of its own. The Mathlib `IsNoetherian` class was also read.
- `def-weil-irreducible-components`: its Mathlib match points to
  `Mathlib.Topology.Irreducible`, `IsIrreducible` / `irreducibleComponents`;
  `IsGenericPoint` was read in `Mathlib.Topology.Sober`. This statement needs
  irreducibility of T, not the stronger assertion that T is an irreducible component.
- `pqf-def-coherent`: `Sheaf.AlgebraicGeometry.Coherent`,
  `AlgebraicGeometry.RingedSpace.IsCoherent`; the whole definition and docstring were
  read. Quasi-coherence is its recorded Mathlib `SheafOfModules.IsQuasicoherent`.
- `def-weil-pbc-closed-subset-proper-over-base`: its recorded module and docstrings
  use the exact inline support locus adopted here. Its proper-over-base definitions
  are not needed and hence that module is not imported.
- `def-weil-pbc-module-stalk`: `Sheaf.Topology.PresheafModuleStalkFunctor`,
  `PresheafOfModules.moduleStalkFunctor` and the underlying Mathlib stalk module
  structure were read. Support uses Mathlib's underlying stalk. The stalk-ring
  scalar action is supplied by the already landed specialization below.
- Added existing landed dependency `def-pc-module-stalk-functor`:
  `Sheaf.Algebra.Homology.ModuleStalkFunctor`,
  `AlgebraicGeometry.RingedSpace.moduleStalkFunctor`. Its full module and node were
  read. This is the same stalk with its O_{X,ξ}-module structure; no replacement
  dependency module or new definition is needed.
- `def-weil-closed-immersion`: Mathlib match
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `AlgebraicGeometry.IsClosedImmersion` (closed embedding and surjective stalk maps).
- `def-pc-integral-scheme`: `Mathlib.AlgebraicGeometry.Properties`,
  `AlgebraicGeometry.IsIntegral`, with nonempty carrier and domain sections.
- `def-pc-module-pullback`: `Sheaf.AlgebraicGeometry.TensorPullback` and its full
  definitions/docstrings were read. This node only needs the right adjoint mentioned
  there, `AlgebraicGeometry.Scheme.Modules.pushforward`, already defined in
  `Mathlib.AlgebraicGeometry.Modules.Sheaf`; no tensor-pullback import is needed.
- `def-weil-residue-field`: `Mathlib.AlgebraicGeometry.ResidueField`,
  `AlgebraicGeometry.Scheme.residueField` and `Scheme.residue`; the residue field is
  the quotient of the stalk by its maximal ideal and the residue map is surjective.
- Exact sequences use `Mathlib.Algebra.Homology.ShortComplex.ShortExact`,
  `CategoryTheory.ShortComplex.ShortExact`, whose complete definition was read.

Edge cases checked before writing:

- The empty scheme and empty T cannot satisfy the generic-point / irreducibility
  assumptions, exactly as in the node and source.
- The zero module is permitted as F; the zero ideal is included in (2).
  G cannot be zero because its generic stalk has dimension one.
- T may be a singleton or all of X; no component-maximality or properness of T is
  assumed. In the absence of smaller integral closed subschemes (2) is vacuous,
  as it is for an integral one-point scheme; (1) and G still supply P(0).
- No reducedness or integrality of X is imposed. Only the tested closed subschemes
  Z are integral. The maximal ideal annihilation is retained even for a nonreduced X.
- Higher-dimensional or infinite-dimensional generic stalks do not satisfy (3)(c).
- One explicit universe u is used for X and all tested Z. Closed subschemes of X
  are representable at this same universe; no independent smaller test universe
  creates vacuous quantification. All variables and universes are explicitly bound.

Searches for an existing statement (2026-10-11):

- `msearch.py ... leansearch "coherent sheaf property irreducible closed support
  devissage generic rank one"`: UNAVAILABLE, Internal Server Error. No verdict
  inferred from this unavailable service.
- `msearch.py ... leanfinder "coherent module property devissage irreducible closed
  support generic stalk rank one"`: eight module support/rank-at-stalk results,
  including `Module.rankAtStalk_pos_iff_mem_support`; none is the sheaf devissage statement.
- `msearch.py ... loogle "IsCoherent, IsIrreducible"`: zero hits, unknown identifier
  `IsCoherent`; not treated as evidence that no coherent declaration exists.
- `msearch.py ... grep "property_irreducible|devissage|IsCoherent" AlgebraicGeometry`:
  zero Mathlib matches. Local reads locate the project's existing coherence definition.
- `rg` of `WeilConjectures` and `lean/Sheaf` for the item id and property-irreducible /
  devissage: no matching statement; unrelated prime-factor and open-closed devissage
  lemmas are present. Grep of the exact proposed full-name suffix
  `coherent_property_irreducible` in Mathlib, upstream, Sheaf, and
  `dag/lean_names_upstream.json`: no collision.
- Reads of existing generic-ideal-inclusion and coherent-filtration modules confirmed
  shared coherence, stalk, support and pushforward encodings. The ideal inclusion
  here uses the existing unit sheaf and quasi-coherence predicate directly and adds
  no copy of `IdealSheafData` or its module construction.

Node fault: proof step 1's parenthetical says P(0) follows from the sequence
0 → 0 → 0 → 0. Two-out-of-three applied there without any known property is tautological.
Instead use the distinguished G and the identity sequence G → G → 0. This repairs
only the natural-language explanation in the new theorem docstring; the node's theorem
statement is correct, so no statement correction or `STATEMENT-DISPUTED` is required.
The node's statement and proof fields are unchanged. Its `stmt_deps` gains only the
existing landed stalk-functor node, as brief-stage2 §5 permits.

Validation: server single-file compile passed without warnings (2.3 s).

## Second reading by C1

I opened the node, the Stacks source at Lemma 30.12.5 (Tag 01YH), and the Lean
module. The correspondence is:

- `X : Scheme.{u}` with `[IsLocallyNoetherian X] [CompactSpace X]` is the
  Noetherian scheme (locally Noetherian and quasi-compact).
- `T : Set X`, `hTclosed`, `hTirreducible`, `ξ : X`, and `hξ` are the closed
  irreducible subset and its generic point.
- `P : X.Modules → Prop` is the arbitrary property; `hshort` quantifies over
  `ShortComplex X.Modules`, requires `ShortExact`, coherence and support in `T`
  for all three terms, and gives the three two-out-of-three implications.
- `hsmaller` quantifies over a same-universe scheme `Z`, a closed immersion
  `i : Z ⟶ X`, `IsIntegral Z`, and the strict image inclusion
  `Set.range i.base ⊂ T`; its final quantifiers encode every quasi-coherent ideal
  as a monomorphism into `SheafOfModules.unit Z.ringCatSheaf` and assert `P` after
  `pushforward i`.
- `hG` gives a coherent `G`, support equal to `T`, maximal-ideal annihilation at
  `ξ`, an explicitly compatible `Module (X.residueField ξ)` structure on the same
  stalk with `Module.finrank = 1`, and `P G`.
- The conclusion quantifies every coherent `F` whose inline nonzero-stalk locus
  is contained in `T` and asserts `P F`.

The quantifier order, objects, support convention, and all conclusion clauses
match the node and source. Edge cases checked: empty `T`/scheme are excluded by
the generic-point and irreducibility hypotheses; zero `F` and zero ideals remain
allowed; `G` cannot be zero because its generic stalk has finrank one; `T` may be
all of `X` or a singleton; no reducedness, integrality, separatedness, or
characteristic assumption on `X` was added; and all test schemes use the scheme's
universe.

Searches (LeanSearch, LeanFinder/Loogle, and grep of Mathlib, `WeilConjectures`,
and `lean/Sheaf`) found no existing property-irreducible statement or name
collision. The existing `def-pc-module-stalk-functor` declaration was read and
added to `stmt_deps`; the module imports and uses its `RingedSpace.moduleStalkFunctor`.

The only mismatch found was in the proof prose: the node's first proof step says
that `P(0)` follows from `0 → 0 → 0 → 0`, which is invalid without an already
known property. I repaired the theorem docstring to use the valid identity
sequence `G → G → 0`; no theorem statement or node proof field was changed.
The module compiles cleanly with only its permitted `sorry` proof warning.
