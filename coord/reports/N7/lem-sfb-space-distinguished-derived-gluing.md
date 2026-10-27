## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceDistinguishedDerivedGluing` states
`AlgebraicGeometry.AlgebraicSpace.space_distinguished_derived_gluing` with one `sorry`.
No theorem is proved and no new definition or dependency module is introduced.
The source read is `literature/stacks-project/spaces-perfect.tex`,
`lemma-glue` (Tag 08HB), both assertions, and
`lemma-make-more-elementary-distinguished-squares` (Tag 08GN), clause (2).

Clause-by-clause correspondence:

- The universe convention is rendered by explicit `universe u w`, `S : Scheme.{u}`,
  and the four `HasDerivedCategory.{w}` instances for the participating primed spaces.
  The small affine ringed models preserve the original module/coefficient universe;
  their module equivalences are those of the already recorded dependency. No equality
  between the site object universe and its morphism universe is assumed.
- Schemes and algebraic spaces are `Scheme` and `AlgebraicSpace S`.
  `W,U,V` are the unprimed spaces, with morphisms `j,p` over `S`.
- The open-subspace hypothesis is `hj`, representability by open immersions on every
  scheme test. This is exactly the condition in `OpenSubspace`, expressed on its
  given algebraic-space presentation; it permits every open subspace.
- The representable-etale hypothesis is `hp : IsEtale p.hom.hom`.
- The reduced complement is `Z : ClosedSubspace W`, `hZ : IsReduced ...`, and
  `hSupport : pointImage ... = (pointImage j.hom.hom)ᶜ`. The point images and
  topology are the dependency's field-valued point classes with their atlas topology.
- The distinguished-square condition is `hIso`, invertibility of the projection
  `V ×_W Z → Z` in the sheaf category. Forgetting the full subcategory of algebraic
  spaces reflects this isomorphism, so this is the stated condition.
- Every base change `t : W' ⟶ W` is allowed. `hU` and `hV` express the defining
  cartesian squares for `U'` and `V'`. No property of `t` is assumed. Arbitrary
  cartesian presentations cover, in particular, the chosen sheaf fibre products.
- The first three conclusions state that `j'` is open, `p'` is representable etale,
  and there exists a reduced closed complement `Z'` with the required support and
  invertible `V' ×_W' Z' → Z'`. They do not assert that `Z ×_W W'` is reduced.
- `T',q,k,hT` are the cartesian overlap `U' ×_W' V'` with its two projections.
- `A : U'.DerivedModules`, `B : V'.DerivedModules`, and `c` give precisely the
  two unbounded structure-module derived objects and their specified overlap iso.
  All pullbacks are the existing `spaceDerivedPullback`, computed by flat-term
  K-flat resolutions and identified with exact restriction for etale morphisms by
  `SpaceDerivedEtaleChartCalculus`. The right derived image in the proof plan is
  the fixed K-injective `derivedDirectImage`; no replacement is chosen.
- The existential `F,f,g` gives the global derived object and both specified
  isomorphisms. Write alpha for the displayed composite of the inverse of
  `spaceDerivedPullbackComp j' q`, the `eqToIso` from `hT.w`, and
  `spaceDerivedPullbackComp p' k`.
  Its orientation is `q* j'* ≅ k* p'*`. The first equation is
  `alpha_F ≫ k*(g.hom) = q*(f.hom) ≫ c.hom`, namely `g|T = c ∘ f|T`
  after the canonical identification. This also gives the source equation
  `c = g|T ∘ f⁻¹|T` by composing with the inverse of `f`.
- For every `M,a,b`, the arrow `a` has type `A → j'*M`, and `b` has type
  `B → p'*M`. Their compatibility is exactly
  `q*a = c.hom ≫ k*b ≫ alpha_M⁻¹`, with no arbitrary comparison map.
- The final existential `d : F ⟶ M` has the two equations
  `j'*d = f.hom ≫ a`, `p'*d = g.hom ≫ b`. The same `F,f,g` works for all such
  compatible target data, as in the source's final paragraph and the node's step 8.
- No boundedness, quasi-coherence, perfectness, quasi-compactness, separation or
  flatness condition is imposed on any object or space.

Dependency declarations read and used (namespace `AlgebraicGeometry.AlgebraicSpace`
unless stated otherwise):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`,
  `IsRepresentableWith`, `IsEtale`, `Modules`, and the actual etale `pullback`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`:
  `ModuleDirectImageModel`, `moduleDirectImage`, `moduleTensorPullback`,
  `moduleTensorAdjunction`; the canonical operations used by the shared derivation.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace`: `OpenSubspace`.
- `Sheaf.AlgebraicGeometry.ReducedClosedSubspaceSupport`:
  `exists_unique_reduced_closed_subspace`; its existing `ClosedSubspace` and
  `IsReduced` interfaces are used for the distinguished complements.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `pointImage`,
  `pointTopologicalSpace`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules`: `DerivedModules`,
  `derivedDirectImage`, using `SmallModules` and `smallModuleEquivalence` from
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel`.
- `Sheaf.AlgebraicGeometry.SpaceDerivedPullback`: `spaceDerivedPullback`,
  `spaceDerivedPullbackComp`, with their fixed universal derived counits.
- `Sheaf.AlgebraicGeometry.SpaceDerivedEtaleChartCalculus`:
  `spaceEtaleDerivedRestriction`,
  `spaceEtaleDerivedRestriction_existsUnique`, and the normalized base-change
  and adjunction computation declarations. This is a plain proof import;
  no declaration owned by this theorem node occurs in the signature.

Added only two already-landed statement dependencies: the definition nodes
`def-sfb-space-derived-module-calculus` and `def-sfb-space-derived-pullback`.
`lem-sfb-space-derived-etale-chart-calculus` remains solely a proof dependency.
These name exactly the canonical interfaces used in the statement. The node's
statement, proof and proof dependencies are unchanged. No correction is needed.

Proof-dependency modules are imported plainly: `ChartwiseEtalePermanence`,
`ElementaryEtaleShriekExact`, Mathlib's `DerivedCategory.ExactFunctor`,
`DerivedCategory.ShortExact`, `Triangulated.Pretriangulated`,
`Triangulated.Triangulated`, `Localization.Adjunction`, and
`SpaceDerivedEtaleChartCalculus`. The reduced-support module remains a public
import for the inherited statement dependency.
`lem-sfb-space-supported-etale-excision` has no recorded Lean declaration in the
read DAG, so there is no module to import for that future proof input.

Edge cases checked against the mathematical statement and the displayed types:
`U = W` gives empty reduced complement; `U` empty forces the etale neighbourhood
above the whole reduced support to be an isomorphism there. Empty `W'` and empty
`T'` are permitted, as are zero `A,B,M` and the identity base change. In the empty
overlap case all compatibility equations live in the zero module derived category.
Nonreduced, nonflat base changes still take their own reduced complement. Arbitrary
negative and positive cohomological degrees are allowed by `DerivedModules`; there
is no truncation or nonemptiness assumption. The overlap comparison's inverse in
the compatibility of `a,b` has precisely the necessary source and target.

Searches actually made:

- `msearch.py ... leanfinder "Glue unbounded derived objects and compatible maps
  along an elementary distinguished square of algebraic spaces"`: eight results
  concern gluing schemes or their morphisms, not this derived gluing theorem.
- `msearch.py ... loogle "DerivedCategory, IsPullback"`: zero hits, with
  `unknown identifier 'IsPullback'`; this query is inconclusive, not a proof of absence.
- `msearch.py ... grep "distinguished.*glue|glue.*derived|derived.*glue"`:
  zero Mathlib hits.
- Direct `rg` over `lean/WeilConjectures` and `lean/Sheaf` for gluing/derived
  terminology found existing `DerivedOpenGluing`, `DerivedOpenGluingObjects`, and
  scheme Hom gluing modules. Their two-open scheme statements do not cover
  arbitrary representable etale distinguished neighbourhoods of algebraic spaces.
- Direct `rg` for `lem-sfb-space-distinguished-derived-gluing` over
  `lean/WeilConjectures`, `lean/Sheaf`, `literature/blueprint/latest`, and
  `dag/lean_names_upstream.json` found no attached declaration.
- Direct `rg` for the proposed declaration name over Mathlib, `WeilConjectures`,
  `Sheaf`, and `dag/lean_names_upstream.json` found no duplicate.

## Repair of returned delivery 0c92ed861b3f

H2: removed `lem-sfb-space-derived-etale-chart-calculus` from `stmt_deps`.
Both occurrences of its plain helper `spaceDerivedChartPullbackSquare` in the
signature are replaced by its defining composite:
`(spaceDerivedPullbackComp j' q).symm` followed by
`eqToIso (congrArg spaceDerivedPullback hT.w)` followed by
`spaceDerivedPullbackComp p' k`. These are exactly the operations owned by
`def-sfb-space-derived-pullback`; no new definition is introduced.
The chart-calculus module is now a plain proof import, since its theorem remains
an existing proof dependency. The source definition at lines 158–167 was read:
the replacement is its body verbatim after specializing the four arrows and the
cartesian commutativity equation. Thus the comparison orientation, both overlap
equations, quantifiers, and all geometric hypotheses are unchanged.

Compared the retained sandbox node with current main before the repair; retained
all current main metadata and changed only `lean` and the two added definition
references in `stmt_deps`. The `lean.statement` is regenerated verbatim from the
repaired signature. Compilation and delivery preflight are rerun for this repair.

## Second reading by N7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
