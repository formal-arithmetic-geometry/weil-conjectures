## Worker report

The module `Sheaf.AlgebraicGeometry.CompletedBaseAffineEtaleSpan` states
`AlgebraicGeometry.completedBaseAffineEtaleSpan`. Its only theorem proof is `sorry`.
No definitions, extra nodes, dependency repairs, or statement corrections are introduced.
The node copy changes only `lean`.

Source checked: `literature/stacks-project/more-morphisms.tex`,
`lemma-relative-map-approximation-pre` (Tag 0GDX), especially its first proof
paragraph at lines 11205–11217, and `lemma-isomorphism-approximation` (Tag 0CAV).
The complete local base is a G-ring even without assuming that the original
stalk is a G-ring; the latter assumption in the full 0GDX statement is used
later for descent, outside this item. This node is the inherited auxiliary
completed-base assertion, not the blueprint unit's own statement.

Hypotheses, one by one:

- The affine schemes S=Spec R and T=Spec D are arbitrary `S T : Scheme.{u}`
  with `[IsAffine S] [IsAffine T]`. This is the coordinate-free equivalent:
  `Scheme.isoSpec` identifies each with its affine spectrum, and no choice
  of coordinate presentation appears in the claim. `[IsAffine X] [IsAffine Y]`
  renders the affineness of both families.
- The maps X→S and Y→T are `f` and `g`. Their finite type hypotheses are
  `[LocallyOfFiniteType f] [QuasiCompact f]` and the corresponding pair for g.
- Finite type of the two bases over Spec Z is expressed by the explicit maps
  `sZ,tZ` to `Spec (.of (ULift.{u} ℤ))` and the same two finite type classes.
  The lift puts Z in the universe of the schemes without restricting u.
- The points are `x : X` and `y : Y`. The points s and t are written `f x`
  and `g y`, eliminating exactly the equations x↦s and y↦t. Every choice of
  the source points and their specified images is covered.
- A is `S.presheaf.stalk (f x)` and its completion is Mathlib's
  `AdicCompletion (IsLocalRing.maximalIdeal A) A`. B is its `Spec`.
  No Noetherian, local, or complete hypothesis is added on the completion.
- The local homomorphism is `σ` with `[IsLocalHom σ]`. Between the local
  rings in the situation, locality is precisely preservation of the maximal
  ideal (equivalently nonunits). The induced lambda is the actual composite
  `Spec.map (CommRingCat.ofHom σ) ≫ T.fromSpecStalk (g y)`.
- XB is `f.completionBaseChange (f x)`, the existing canonical pullback;
  YB is the explicit `pullback g lambda`. The point `yB` and equations
  `hyB,hb` say that its projections are y and b.
- The point b is the inverse image of the zero prime of A/m under
  `AdicCompletion.evalOneₐ`. For a Noetherian local A this is exactly the
  unique closed point of B, since the completion maximal ideal is the kernel
  of this map. This expression needs no premature Noetherian instance.
- `hformal` supplies the required ring isomorphism of completed stalks and
  an equation saying it commutes with the canonical completed-base actions.
  The action on the X completion is `Classical.choose
  (RingHom.exists_adicCompletion_map_of_local (f.stalkMap x).hom)`.
  This published theorem fixes every quotient coordinate; thus it determines
  the map uniquely, and its choice is permitted, not arbitrary algebra data.
  The action on the YB completion is constants into the B stalk followed by
  the second projection's stalk map and the canonical completion map.
  An isomorphism of rings commuting with these maps is exactly the given
  isomorphism of completed-base algebras; no coefficient map is a free parameter.

Conclusions, one by one:

- `IsNoetherian (Spec (.of ...))` is the Noetherianity of B, including
  quasi-compactness, rather than only local Noetherianity.
- `IsIso ((S.completionBaseMap (f x)).residueFieldMap b)` is the actual
  canonical κ(s)→κ(b) isomorphism. The canonical base map sends b to s.
- The existential `xB` and the next two equations put xB over (x,b).
  The universal clause over `z` asserts uniqueness among all such points.
- `IsIso ((pullback.fst f ...).residueFieldMap xB)` asserts that the canonical
  κ(x)→κ(xB) map is an isomorphism, using the preceding projection equation.
- `H,h,p,a,c` give the common source, marked point, B-structure map, and
  its two arrows. `IsAffine H` is the required affineness.
- `LocallyOfFinitePresentation p ∧ QuasiCompact p ∧ QuasiSeparated p`
  is finite presentation in exactly the convention node (Stacks 01TP).
- `p h = b` states that the marked point is over b. The two equations
  `a ≫ pullback.snd ... = p` and `c ≫ pullback.snd ... = p` say that a,c
  are B-morphisms for this same structure map.
- `Etale a ∧ Etale c`, `a h = xB ∧ c h = yB` render the two pointed étale maps.
- `IsIso (a.residueFieldMap h) ∧ IsIso (c.residueFieldMap h)` are exactly
  both induced residue-field isomorphisms. IsIso in CommRingCat asserts
  invertibility of these particular maps, not the existence of unrelated field isomorphisms.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `Spec`, `Spec.map`; `Mathlib.AlgebraicGeometry.AffineScheme`: `IsAffine`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Mathlib.RingTheory.AdicCompletion.Basic` / `.Algebra`: `AdicCompletion`,
  its canonical ring/algebra structure and `AdicCompletion.evalOneₐ`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`, `IsNoetherian`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `Scheme.Hom.residueFieldMap`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `LocallyOfFinitePresentation`; `.QuasiSeparated`: `QuasiSeparated`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale`.
- `Sheaf.AlgebraicGeometry.CompletedLocalBaseChange`:
  `Scheme.completionBaseMap`, `Scheme.Hom.completionBaseChange`, and the
  proof dependency `Scheme.completedLocalBaseChange`.
- `WeilConjectures.RingTheory.CompletionMapForLocalHom`:
  `RingHom.exists_adicCompletion_map_of_local` (canonical action specified
  by all finite quotient coordinates, with its full signature and proof read).

The convention dependency defines no separate object and so requires no
standalone module. Its finite-presentation conjunction is used verbatim.
All published non-Mathlib proof-dependency modules are imported, including
UnramifiedMorphism, IsomorphismCompletionApproximation, AdicCompletionNoetherian,
CompleteLocalGRing, and FibreProductPointResidueField. The theorem docstring
carries all six DAG proof steps and their constituent named dependencies.

Edge cases checked: a field base stalk has zero maximal ideal and unchanged
completion; generic and nonclosed x,y are allowed (nothing asserts these points
are closed); the residue extensions can be arbitrary; no positive-dimensional,
characteristic, rationality, or algebraic-closure hypothesis occurs. An empty
X or Y has no marked point and gives no instance of the premise. The closed
base point exists canonically even before Noetherianity is supplied. All scheme
and ring sizes use the single arbitrary u, with Z lifted to u. The uniqueness
clause quantifies over every point of the actual pullback. Finite presentation
includes quasi-separatedness explicitly. No additional G-ring assumption occurs.

Searches made:

- `msearch.py ... leanfinder "Formal isomorphism of completed stalks gives an
  affine etale span over the completed local base"`: 8 hits, consisting of ring
  étale localization/locus facts; no approximation-span theorem.
- `msearch.py ... loogle "AdicCompletion.map, Scheme.Hom.stalkMap,
  IsLocalRing.closedPoint"`: 0 hits; Loogle did not know the abbreviated
  Scheme.Hom.stalkMap name. The actual project and Mathlib sources were read.
- `msearch.py ... grep "completed.*[Ss]pan|completion.*approximation"
  AlgebraicGeometry`: 0 Mathlib hits.
- `rg` with those expressions and canonical completion-map expressions over
  both `lean/WeilConjectures` and `lean/Sheaf`: found the existing canonical
  completed-base helpers, relative-completion approximation, and 0CAV; none
  states this affine finite-presentation span and all its residue/uniqueness clauses.
  The relative approximation module is downstream of this item, so its helpers
  are expressed directly using Spec.map rather than imported to create a cycle.
- The required item-id search in `lean/WeilConjectures` had no hit. Searches
  for `completedBaseAffineEtaleSpan` in the upstream-name index and library
  found no declaration. The current module name/declaration are new.

Validation: scompile.py compiled both the sandbox module and its library-path
version cleanly, 4.0 and 4.6 seconds respectively. The first compile exposed a
category-inference metavariable in the point binder. Adding the explicit
`(C := Scheme.{u})` to that pullback fixed it; the mathematical signature is
unchanged. Every variable and universe is explicit and both auto-implicit
options are disabled. No diagnostic commands or local notation remain.

## Second reading by Q158

This is an author's final consistency check, not an independent review;
the dispatcher explicitly prohibits starting another agent and assigns the
independent review to the maintainer. Re-read the node and the compiled module:
all assumptions, both specified base changes, the canonical scalar compatibility,
Noetherianity, the two initial residue statements, uniqueness, affineness, all
three finite-presentation conditions, the B-morphism triangles, the marked-point
equations and both final residue statements are present as matched above.
No statement mismatch or disputed assertion was found. No DAG statement changes
were made. The sole elaboration repair was the explicit pullback category.
