## Worker report

The delivery states `AlgebraicGeometry.ProperOpenCalculus.compactification_refinement_coherence`
in `Sheaf.AlgebraicGeometry.CompactificationRefinementCoherence`, with its entire proof
`sorry`. The other module defines the abstract proper/open input and the canonical arrows;
none of its data uses `sorry`. The original statement, proof and proof dependencies are
unchanged. The item's statement dependencies gain `def-sp-proper-open-calculus`.

The correspondence with every hypothesis and clause is as follows.

- The category of schemes is specified by `A : Scheme.{u} → Prop`; its objects are
  `{X : Scheme.{u} // A X}`, and its arrows here are actual separated finite-type scheme
  morphisms. `IsSeparated`, `LocallyOfFiniteType` and `QuasiCompact` are explicit for
  each quantified input map. This imposes no qcqs condition on an individual scheme.
  The certificates `hc`, `TriangleObjects` and `TowerObjects` keep every ambient scheme
  in the specified category, instead of requiring data on schemes outside it.
- Compactifications and their arrows are the upstream `Compactification` and
  `Compactification.Refinement`. Properness of a refinement is the existing instance.
  Under `QuasiCompact f`, `Compactification.quasiCompact_openImmersion` supplies exactly
  the quasi-compactness of every compactification open map. No density condition is added.
- The assumed nonempty, cofiltered compactification categories are the `nonempty`,
  `common` and `equalize` fields of `Geometry A`. The equalizing equation is
  `t.comp r = t.comp s`, with no uniqueness or cartesian requirement on parallel arrows.
  Its `compatible` field gives a tower over a prescribed compactification of g refining
  a prescribed compactification of gf. Its `towers` field gives a common refining tower;
  its `staircases` field supplies a three-map staircase. These are propositions assumed
  by the theorem's `Geometry A →`, not geometric conclusions being proved.
- The assigned categories are `F.obj X` with `F.category X`, with independent explicit
  object and morphism universes. The proper functors are `F.P`; the open functors are
  `F.J`. Opens among separated finite-type arrows are precisely quasi-compact open
  immersions, so `J` requires `QuasiCompact j`; no functor on a non-finite-type open is
  silently demanded. The identity and associative composition data are `pId`, `jId`,
  `pComp`, `jComp`, `pAssoc`, `jAssoc`, `pLeft`, `pRight`, `jLeft`, `jRight`.
- A square's specified invertible interchange is `F.gamma U V W Z k r p i h`, with
  `h : k ≫ p = r ≫ i`. Its orientation is `P_r ⋙ J_i ≅ J_k ⋙ P_p` in Lean's
  left-to-right functor-composition convention. `vertical` and `horizontal` are exactly
  the two displayed pasting formulas from the varying-ring node, as assumptions on
  arbitrary data. `verticalIdentity` and `horizontalIdentity` are the two identity-square
  laws with their respective unit identifications. The equations quantify over every
  object; natural transformations are determined by these components.
- `H` is the actual definition `J_j ⋙ P_p`. `rho` first inserts the inverse proper
  identity isomorphism, then uses the gamma of `r ∘ j_d = j_c ∘ id_X`, then uses the proper compositor. Its Lean
  square equality is `d.i ≫ r.hom = (𝟙 X) ≫ c.i`. The map is built as an isomorphism
  from these factors, not chosen from an existence assertion. No cartesianness is used.
- The first and second theorem conjuncts give rho of identity and composition. In the
  second, `s.comp r` means the refinement `e → d → c`, and the result is
  `rho r ≪≫ rho s`, with source `H_c` and target `H_e`.
- `compare h₁ h₂ hd r₁ r₂` is literally `rho r₂ ≪≫ (rho r₁).symm`, from `H_c₂`
  to `H_c₁`. The third conjunct quantifies independently over both common refinements
  and all four arrows and equates the resulting isomorphisms. The fourth quantifies
  over three separately supplied common refinements and gives `T₂₃ ≪≫ T₁₂ = T₁₃`,
  which is precisely the paper's right-to-left cocycle law.
- The compatible binary tower is upstream `Compactification.Triangle`. Its fields
  `cg.i`, `cg.g`, `cfg.i`, `p`, `q`, `cf.g`, `cf.i` are respectively the node's
  `i`, `q`, `a`, `p`, `b`, `r`, `j`. `isPullback` represents the intermediate fibre
  product up to its unique projection-compatible isomorphism. `towerIso` is the actual
  whiskered gamma followed by the open and proper compositors; the definition exposes
  every associator. The intermediate open's quasi-compactness is supplied by the existing
  base-change theorem `MorphismProperty.of_isPullback`.
- `TowerRefinement R T` contains the three upstream refinements and the two tower
  compatibility squares. Together with the refinement equations these are all seven
  equations listed in the node's proof Step 5. No `Triangle.Hom` is used, since it
  would impose additional cartesian conditions. The fifth conjunct compares ANY two
  towers and ANY two maps from ANY common refining tower, on all three factors, as
  an equality of actual natural transformations using `NatTrans.hcomp`.
- The sixth conjunct uses upstream `Compactification.Tower` and its four triangles
  `fg`, `gh`, `fg_h`, `f_gh`. It equates the two iterated `towerIso` transformations
  with the functor associator explicitly inserted. Combining this equation with the
  preceding arbitrary-tower comparison and the cocycle gives the equation for arbitrary
  choices of the binary towers, exactly as node proof Step 11 explains. Ambient
  compactifications of `(f ≫ g) ≫ h` and `f ≫ g ≫ h` differ only in their proof of
  the factorization equation; their H functors are definitionally the same.
- The seventh and eighth conjuncts give the two trivial identity towers `unitLeft`
  and `unitRight`. Their right-hand sides use the constructed `identityIso` and the
  ordinary functor unitors. The arbitrary-tower comparison transports these to any
  other identity towers, as in Step 11. Invertibility is built into the supplied gamma
  and compositors; no coefficient-specific invertibility theorem is asserted.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper`, `IsSeparated`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`, with
  `QuasiCompact` for finite type, as prescribed by the recorded dependency.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback` and its
  projections; the imported upstream `Triangle`/`Tower` expose their universal property
  through `IsPullback`, allowing any scheme representing the specified fibre product.
- `WeilConjectures.Compactification.Defs` and `.Refinement`: `Compactification`,
  `quasiCompact_openImmersion`, `Refinement`, `Refinement.id`, `Refinement.comp`.
- `WeilConjectures.Compactification.Triangle` and `.Tower`: the geometric objects,
  four staircase triangles, and the two identity triangles.
- `Sheaf.AlgebraicGeometry.CompactifiableCompatibleTower`:
  `exists_compactifiable_compatible_tower`, read in full; its same geometric hypotheses
  and diagrams are assumed through `Geometry` rather than replaced by a new theorem.
- `WeilConjectures.Compactification.CategoryBaseChange` and `.Cofiltered`:
  `baseChangeFunctor`, `Refinement.baseChange_id`, `Refinement.baseChange_comp`,
  `isCofiltered`, and `quasiCompact_openImmersion_iff`, read at the recorded source.
- `Sheaf.AlgebraicGeometry.VaryingRingProperOpenPasting`:
  `AlgebraicGeometry.ProEtale.VaryingRing.properOpenPasting`, `gamma_identities` were
  read as the concrete equations referred to by the node. Their exact abstract forms
  are the fields of the NEW datum, not replacements for these coefficient-specific
  declarations. No inverse ring sequence is part of this formal statement. The concrete
  varying-ring module is therefore not imported: it supplies the axiom template, not
  an input construction used here. An attempted import was also confirmed by scompile
  to hit unrelated existing universe errors in `Sheaf.Paper.SemilinearSystemModels`;
  no live module or launcher tool was changed.

Edge cases checked: A may be empty; the theorem then has no scheme instances, as its
informal quantification does. A coefficient category may be empty or trivial. Empty schemes
are allowed. Identity maps, identical compactifications, zero-length refinement chains,
nonunique parallel refinement arrows, and noncartesian refinements are all retained.
The two identity towers and both parenthesizations of a triple composite are explicitly
present. Neither scheme size nor the size of the categories is tied to the other. No
Noetherian, field, finite-coefficient, density, characteristic, or qcqs hypothesis is added.

Searches: msearch LeanFinder query “Coherent proper and open functor interchange yields
compactification refinement independence and associative composition” returned eight
unrelated condensed/topological declarations; Loogle `"Compactification"` returned zero.
The Mathlib AlgebraicGeometry grep `compactification|compactifiable|ProperOpenCalculus`
returned zero. For the new datum, LeanSearch “proper open covariant functors coherent
interchange compactification calculus” returned eight unrelated topology/coherent-site
hits, and the CategoryTheory grep `ProperOpenCalculus|CompactificationCalculus|proper.open.*datum`
returned zero. Direct rg in DAG, upstream `WeilConjectures`, and `lean/Sheaf`, and blueprint
searches were also performed. Exact search outputs are in the new node's `mathlib_searches`.
The existing upstream `CompactSupportFormalism` requires pullback adjunctions and its
refinement comparison requires a cartesian square, so it cannot state this arbitrary-data
result. Existing coefficient-specific strict/varying tower calculi likewise do not supply
this notion. The requested upstream search for the item's id found no declaration.

The module docstring includes the entire eleven-step natural-language proof of the node.
There is one postponed theorem, and its matching DAG node is this item. There is no
statement dispute, correction, or dependency-module replacement.

## New nodes

`def-sp-proper-open-calculus` records the missing abstract P,J,gamma datum, its precise
unit/associativity/pasting axioms, and its own canonical H/rho/common-refinement/binary-tower
constructions and geometric-existence predicate. It is sourced from Stacks 0F7C, 0F7D,
0F7J and 0F7K, with the same arbitrary-scheme supplied-data intent as the item. The
upstream adjunction formalism and concrete coefficient constructions have stronger input
requirements and are not the same notion. Existing compactifications, refinements,
triangles and staircases are reused, not redefined. The small membership predicates
and weak tower-refinement record only expose the ambient collection and the exact
seven compatibility equations. All searches and all ten public declarations are recorded.

## Second reading by Q02

I reread the node, the two modules, and the cited Stacks proof, separately from the initial
writing pass. This is the dispatcher's single-worker second pass; the maintainer supplies
the independent review, as specified in the brief. No second agent was started.

I checked the orientation of rho against `r.i_hom` and `r.hom_g`, and the order of the
common-refinement comparison against the node's formula: the latter really goes from c₂
to c₁. I checked all eight conjuncts against the clauses listed above, including the
independent choices of all common-refinement arrows, the three input/output comparisons
in the binary-tower square, and the associator in the staircase equation. I checked the
unit equations against both `Triangle.unitLeft` and `Triangle.unitRight`.

The reading caught and repaired an unnecessary demand for J on non-quasi-compact opens:
the ambient maps are finite type, so J and its pasting axioms now use quasi-compact opens.
Named existing quasi-compactness and base-change theorems supply these instances in the
constructed definitions; no new hypothesis is placed on a compactification. I also
replaced the upstream cartesian `Triangle.Hom` interface with the exact weaker record
of the already stated tower-refinement notion. I checked that this record demands
only the seven equations, not cartesianness of arbitrary refinements.

Both definition data and statement universes are explicitly bound. The only scoped linter
option suppresses the standard structure-universe linter, as the upstream abstract
formalism does; no style or proof warning is suppressed. Every line is within 100 columns.

Validation: the final two modules compile warning-free through scompile.py. The required
deliver2.py --no-push dry run passed server preflight and per-file compilation with
exactly the two modules, the two node records and this report.
