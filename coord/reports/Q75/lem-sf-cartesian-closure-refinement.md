## Worker report

The module `Sheaf.Compactification.CartesianClosureRefinement` states
`AlgebraicGeometry.cartesian_closure_refinement`. Its single proof is `sorry`.
No definitions, helper axioms, new nodes, dependency modules or statement corrections
are introduced. The node copy changes only `lean`.

The source read was blueprint main-20261015,
`sec-nagata-compactification/sk-lem-nagata-sketch-closure/_section.md` and all six
accepted proof steps of this item. The geometric extension of the closure result
is the node's relative-properness/clopen-complement argument. The docstring reproduces
all six steps and their dependency names.

Hypotheses and clauses, matched to the Lean signature:

- Field: `(k : Type u) [Field k]`.
- Five finite-type k-schemes: `(X V Xbar Y Ybar : Scheme.{u})`, their five explicitly
  bound structure maps `sX`, `sV`, `sXbar`, `sY`, `sYbar` to `Spec (.of k)`, and
  `LocallyOfFiniteType` and `QuasiCompact` for EACH structure map. This is precisely
  the recorded finite-type convention. There is no separatedness assumption.
- The three open immersions: `j`, `b`, `i` with their `IsOpenImmersion` instances.
- Proper maps: `q`, `p` with `IsProper q`, `IsProper p`.
- Commutative supplied square: `_hcomm : b ≫ p = q ≫ i`. No Cartesian hypothesis is
  imposed, and no compatibility with the five chosen structure maps is needed or added.
- The prescribed scheme-theoretic closure W, inclusion a and factor X → W are the
  existing canonical constructions `(j ≫ b).image`, `(j ≫ b).imageι`,
  `(j ≫ b).toImage`. These retain the scheme structure, not a reduced/topological
  replacement. `nagata_sketch_closure` characterizes this image as the smallest
  closed factorization; its source module and full statement were read.
- W_Y is exactly `pullback ((j ≫ b).imageι ≫ p) i`. Its projections b' and q' are
  `pullback.fst` and `pullback.snd` with those arguments throughout the signature.
- The closedness of a is `IsClosedImmersion (j ≫ b).imageι`.
- The open, schematically dense map X → W is `IsOpenImmersion (j ≫ b).toImage` and
  injectivity of `(j ≫ b).toImage.app U` for EVERY open `U` of the image. This uses
  precisely the sectionwise density convention of `nagata_sketch_closure`.
- Properness of a and pa are the next two `IsProper` conjuncts.
- b' is an open immersion and q' is proper by the next two conjuncts.
- The square is Cartesian by the `IsPullback` conjunct, ordered as the square
  W_Y → W above Y → Ybar. This is the transpose convention of the drawn square.
- The empty case is explicit: `IsEmpty X → IsEmpty (j ≫ b).image ∧
  IsEmpty (pullback ((j ≫ b).imageι ≫ p) i : Scheme.{u})`.
- The required j' and v are existentially quantified morphisms on this specified
  pullback, with `IsOpenImmersion j'`, `QuasiCompact j'`,
  `IsClosedImmersion v`, and `IsProper v`.
- The four requested identities are, respectively, `j' ≫ v = j`,
  `v ≫ b = pullback.fst ... ≫ (j ≫ b).imageι`,
  `v ≫ q = pullback.snd ...`, and
  `pullback.fst ... ≫ ((j ≫ b).imageι ≫ p) = pullback.snd ... ≫ i`.
  The fourth is retained because the node explicitly requests it, although it is
  also the defining pullback equation.
- The last two identities specify that j' is the factor of the canonical map
  X → W and is over the given X → Y. Together with the four displayed identities,
  proper a and v, they express the stated refining triangles with identity on X
  and Y. This is the concrete morphism data of `Compactification.Refinement`;
  that recorded interface is imported, without introducing another refinement
  notion. No arbitrary closure or factor morphism is substituted for the canonical one.

Dependency interfaces read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`, and the base-change
  projection instances (for the proof plan).
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper`, composition and
  pullback projection instances, `IsProper.of_comp`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`, `pullback.lift`; scheme existence is imported via
  `Mathlib.AlgebraicGeometry.Pullbacks`.
- `Sheaf.Compactification.NagataSketchClosure`: `nagata_sketch_closure`;
  its public image constructions come from
  `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`: `Scheme.Hom.image`,
  `Scheme.Hom.imageι`, `Scheme.Hom.toImage`.
- `WeilConjectures.Compactification.RefinementCategory`:
  `Compactification.Refinement`, `Compactification.category`; full structure
  signatures and docstrings read, including automatic properness of a refinement.
- Proof dependencies in `Mathlib.AlgebraicGeometry.Noetherian`:
  `LocallyOfFiniteType.isLocallyNoetherian`, `IsNoetherian`,
  `IsNoetherian.noetherianSpace`, `IsLocallyNoetherian.quasiSeparatedSpace`, and the
  open-subscheme locally Noetherian instance. The quasi-compactness ingredient is
  `QuasiCompact.compactSpace_of_compactSpace` in Morphisms.QuasiCompact.
- `Mathlib.AlgebraicGeometry.Morphisms.Immersion`:
  `IsImmersion.instIsOpenImmersionToImageOfQuasiCompact` (the anonymous instance
  in the current source), together with image quasi-compactness and density from
  IdealSheaf.Subscheme. No reducedness is required.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Proper`:
  `IsProper.pullback_snd`, `IsProper.of_isClosedImmersion`,
  `IsProper.isClosedImmersion_comp`.
- The proof-only recorded module of `lem-pc-closed-imm-base-change`,
  `WeilConjectures.AlgebraicGeometry.Modules.VeryAmple`, is imported as required.
  Its recorded `IsVeryAmple.pullback_of_field` was read: it proves a very-ampleness
  application of closed-immersion base change, rather than the full node. The
  closed-immersion base-change clause actually needed here is already a Mathlib
  instance in Morphisms.ClosedImmersion. This is a proof-only attachment issue;
  no unusable statement dependency or replacement notion is involved.

Edge cases checked before writing: X empty gives empty schematic image and empty
pullback; all identities remain meaningful. If X = V, the proper open immersion
V into Xbar ×_Ybar Y is clopen, so its closure restricts back to V. Identity b or i
also gives the expected restricted closure. Extra components over Y are removed
by the clopen-complement argument; no Cartesian assumption is smuggled into the
input. Nonreduced schemes use the kernel subscheme, retaining nilpotents.
Nonseparated structure maps to k are allowed; only the RELATIVE proper projection
to Y is used for separatedness. All schemes and k share the standard scheme
universe u, which may be arbitrarily large. No variables or universes are implicit.

Searches performed:

- `msearch.py ... leanfinder "Schematic closure of an open subscheme refines a
  proper open triangle to a Cartesian square"`: 8 hits, led by
  `IsImmersion.isPullback_toImage_liftCoborder` and `Scheme.Hom.liftCoborder`;
  these give component geometry, not the supplied triangle or all its conclusions.
  An interrupted initial search process was no longer available; the completed
  repeat produced these results.
- `msearch.py ... loogle "AlgebraicGeometry.IsProper,
  AlgebraicGeometry.IsOpenImmersion"`: OK, 0 hits.
- `msearch.py ... grep "cartesian.*[Cc]losure|closure.*[Rr]efinement|toImage"
  AlgebraicGeometry`: OK, 25 hits, including image constructions and
  `isPullback_toImage_liftCoborder`; no complete match.
- `rg` over both `lean/WeilConjectures` and `lean/Sheaf` for
  `cartesian.*[Cc]losure|closure.*[Rr]efinement|lem-sf-cartesian-closure-refinement|schematicClosure`:
  no existing declaration for this node. The refinement and common-refinement
  comments led to reading Compactification.OverRefinement and RefinementCategory.
  `OverRefinement.isPullback_of_isProper_of_isSchemeTheoreticallyDominant` concerns
  a dense compactification of an already proper map; it does not state the
  current general non-Cartesian triangle with j and the specified closure.

Validation: `scompile.py Q75 lem-sf-cartesian-closure-refinement <module>` passed
both the sandbox and named library compile, with no errors or non-sorry warnings.
The first probe needed the explicit `: Scheme.{u}` coercion for the pullback
inside `IsEmpty`; repaired before the clean compile. No statement fault or
STATEMENT-DISPUTED flag remains.

## Second reading by Q75

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
