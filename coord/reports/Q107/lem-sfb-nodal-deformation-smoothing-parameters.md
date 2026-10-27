## Worker report

The module `Sheaf.AlgebraicGeometry.NodalDeformationSmoothingParameters` states
`AlgebraicGeometry.NodalDeformation.exists_smoothing`, with proof `sorry`.
Its `Smoothing` structure packages the conclusions, not hypotheses assumed about a
pre-existing deformation ring. All definitions have actual data. There is one theorem;
its docstring gives the twelve-step accepted DAG proof, including all intermediate
arguments. All already recorded proof dependencies are imported with plain imports;
statement dependencies use public imports.

Source read: Deligne--Mumford, The irreducibility of the space of curves of given
genus, §1, printed pp.79--83, Lemmas 1.3--1.4, Proposition 1.5, Theorem 1.6 and
Corollary 1.9, at https://www.numdam.org/item/PMIHES_1969__36__75_0.pdf .
This is the equal-characteristic restriction of the source. The node is not a
blueprint unit statement; no correction of its statement is proposed.

Hypotheses and clauses, matched with the Lean:

- `k : Type u`, `[Field k]`, `[IsAlgClosed k]`: algebraically closed field of any
  characteristic. `C : Scheme.{u}` with `[C.Over (Spec (.of k))]` is the k-curve.
- `[ConnectedSpace C]`, `[IsReduced C]`, `[IsHProjective (C ↘ Spec (.of k))]`
  encode connected nonempty, reduced and projective. Properness follows from the
  recorded projective-morphism instance. `hdim : topologicalKrullDim C = 1`
  is dimension one. No smoothness or irreducibility is assumed globally.
- `d`, `q : Fin d → C`, `hq`: exactly the labelled distinct nodes. `hsmooth`
  says the complement is smooth, and `eq` identifies each completed local ring
  with `Node k = k[[x,y]]/(xy)`. `eq_scalar` makes these k-identifications.
  Neither singular points nor a special characteristic are excluded.
- The universal property of the recorded `relativeDifferentials` identifies
  `Subsingleton (relativeDifferentials ⟶ Scheme.Modules.unit C)` with vanishing
  of all k-linear sheaf derivations. This is an implication in the first conjunct,
  so the stable clause can independently conclude vanishing of derivations.
- Artinian residue-marked k-algebras are exactly `ArtinDeformation.TestCategory k k`.
  `Proper f R` is the proper subtype of the existing `SchemeDeformation.Lift`:
  flatness and the specified special-fibre cartesian square are retained.
  `Global f R` takes precisely marking-preserving isomorphism classes.
  `GlobalBC` uses the existing cartesian `SchemeDeformation.IsBaseChange` relation.
  It specifies the actual pullback, rather than a map arbitrarily imposed on classes.
- `Smoothing.ring : CompleteLocalAlgebra k k` supplies complete Noetherian local
  ring, coefficient algebra and residue marking. `represents` are bijections
  from the existing continuous marked local maps `LocalMap ring R`.
  `natural` states base change iff composition of those maps. Local homomorphisms
  are automatically continuous for maximal-ideal-adic topologies.
- `unobstructed` spells out absolute formal smoothness for every surjective test
  map with square-zero kernel; no restriction to principal or small kernels.
- `tangent` identifies the actual dual-number classes with the recorded
  `Scheme.Modules.Ext relativeDifferentials (Scheme.Modules.unit C) 1`.
  `tangent_zero`, `tangent_add`, `tangent_smul` pin the vector-space operations to
  trivial deformation, split-square-zero gluing, and scalar pullback using
  existing `SchemeDeformation` operations. `FiniteDimensional` is concluded,
  not assumed. `[HasExt.{u} C.Modules]` is the standard size witness for the
  recorded Ext definition, available for the Grothendieck module category.
- `LocalObject` is the complete Noetherian local subtype of the existing
  `Algebra.FlatDeformation.Groupoid (Node k) R`; `Local` is its marked isomorphism
  quotient. Isomorphisms of complete local rings are adically continuous.
  `LocalBC` uses the actual marked tensor comparison of that existing interface.
- `restriction` is characterized by `completion`: every representative is sent
  to its completed stalk at the image of the marked node. `IsRestriction`
  specifies its coefficient map and special-fibre map, the latter using the
  existing exact quotientwise `IsCompletionMap`. `restriction_natural` retains
  base change, and `restriction_smooth` quantifies over every compatible pair
  across every square-zero Artinian surjection.
- `localRing`, `localCoordinate`, `localHull`, `hull` give k[[s]], its family
  `Equation R s = R[[x,y]]/(xy-s)`, and its smooth tangent-bijective hull map.
  `HasEquation` fixes the coefficient embedding and reduction marking explicitly.
  No bijectivity at general Artinian bases is asserted for a local node functor.
- `localTangent` and `localTangent_coordinate` identify the local tangent parameter
  with its actual epsilon coefficient. `tangentRestriction` is linear,
  surjective, and agrees with completion on dual numbers. `nodeBound` says d≤N,
  and `relativeTangentDimension` says its kernel has dimension N-d.
- `hullBase`, `hullCoordinates`, `hullMap`, `smoothHullMap` give the product local
  hull k[[s_1,...,s_d]] and its formally smooth map into the representing ring.
  `powerSeries` is the relative power-series presentation with N-d extra
  variables. `powerSeries_base` fixes the map on the whole base ring; continuity
  in both directions is included. `nodeMap` and its coordinate equation specify
  each local hull map; `nodeMap_restriction` ties it to completed restriction for
  every Artinian point. These choices are existential fields of the concluded
  `Nonempty Smoothing`, not arbitrary inputs.
- `effective` applies to every effective proper flat nodal family with the marked
  special fibre whose Artinian restrictions are the represented universal classes.
  It gives the completed equations xy-s_i with the exact structural coefficient
  map. For every field-valued point of the complete base it states that the fibre
  is smooth iff every s_i is nonzero. This is precisely equality of the nonsmooth
  locus with the union V(s_i), excluding extra discriminant components.
- The second conjunct quantifies over g≥2 and the recorded unpointed genus-g
  stable moduli fibre, identified with C as a k-curve. It concludes vanishing of
  derivations and Ext dimension 3g-3. Arithmetic genus is the module-cohomology
  genus in `StablePointedModuli`, not geometric genus of a chosen normalization.

Dependency declarations read and used:

- Mathlib: `Field`; `AlgebraicGeometry.Scheme`, `Scheme.Hom`, `IsProper`, `Flat`,
  `IsReduced`; `MvPowerSeries`; `AdicCompletion`, `IsAdicComplete`.
- `WeilConjectures.AlgebraicGeometry.Modules.Differentials`:
  `Scheme.Hom.relativeDifferentials` (and its documented representing property).
- `WeilConjectures.AlgebraicGeometry.Modules.Ext`: `Scheme.Modules.Ext`.
  `WeilConjectures.AlgebraicGeometry.Modules.Linear`: `linearOfOver`, with Mathlib's
  `CategoryTheory.Abelian.Ext` module structure for the actual scalar action.
- `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`: `IsHProjective`.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`: `StablePointedModuli`,
  `StablePointedModuli.Fiber`; `Sheaf.AlgebraicGeometry.StableFiberCurve`:
  `StablePointedModuli.fiberCurve`.
- `Sheaf.AlgebraicGeometry.ArtinDeformationTestCategory`: `TestCategory`, `ring`,
  `residue`, `map`, `CompleteLocalAlgebra`, `LocalMap`, `squareZeroTest`.
- `Sheaf.AlgebraicGeometry.MarkedSchemeLifts`: `Lift`, its space/projection/marking,
  `IsBaseChange`, `IsTrivial`, `IsSum`, `directionMap`.
- `Sheaf.RingTheory.MarkedFlatAlgebraDeformations`: `Groupoid`, `algebra`, `scalar`,
  `marking`, `IsBaseChange`, `IsCompletionMap`.
- `Sheaf.RingTheory.CompleteLocalSmoothPowerSeries`: `completeAugmentation`,
  `IsFormallySmoothOnArtin`.

The item's statement dependencies gain the already landed nodes for marked scheme
lifts, marked flat algebra deformations, Artinian tests and stable fibre curves;
no new independent notion or dependency replacement is introduced. The helper
vocabulary belongs to this node's own definition of Def_C and its specified local
functors, equations and smoothing conclusions and is listed in lean.declarations.

Edge cases checked before writing: d=0 (all node families and products are empty;
the smooth-fibre test is true everywhere), N=d (zero additional variables), N=0,
self-nodes, reducible curves, characteristic 2 and arbitrary positive characteristic,
the identity Artinian surjection and nonprincipal square-zero kernels. ConnectedSpace
excludes the empty scheme exactly as a connected projective curve does. The stable
clause has no vanishing-derivations antecedent. No genus restriction is imposed on
the general curve. No uniqueness of local parameters over arbitrary Artinian rings
is asserted. Universes are explicitly bound, and autoImplicit is disabled.

Searches actually run:

- msearch LeanFinder: "A proper nodal curve without infinitesimal automorphisms has
  a smooth universal deformation with independent local node smoothing parameters";
  eight hits on ordinary smooth morphisms, none on this deformation theorem.
- msearch Loogle: "MvPowerSeries, Algebra.FormallySmooth"; zero hits.
- msearch grep: "Deformation|deformation|prorepresent", AlgebraicGeometry; zero hits.
- msearch LeanSearch: "proper nodal curve deformation prorepresented power series
  ring local smoothing parameters"; eight hits on power series and ordinary formal
  smoothness, none stating this theorem.
- rg on lean/WeilConjectures and lean/Sheaf for the item id, nodal/deformation
  combinations, Def_C and nodeDeformation: only a proof citation in
  StableLevelVersalBranchFreeness.lean; no duplicate statement.
- Broader rg for prorepresentation and deformation interfaces found the existing
  Artinian test, complete local, marked scheme and marked flat algebra interfaces
  used above. The proper-scheme hull and hypersurface presentation proof nodes
  currently have no Lean record, so they remain unimported proof prerequisites.
- tools/blueprint_refs.py search "nodal deformation": zero blueprint nodes.
  DAG searches for node deformation/proper deformation found this item and the
  strictly more general prerequisite nodes, not an exact existing theorem.
- dag/lean_names_upstream.json search for the item id: no match.

No statement correction or STATEMENT-DISPUTED flag.

## Second reading by Q107

This section records this worker's separate source-to-signature check; the maintainer
supplies the independent delivery review. No other agent was started, as the dispatch
brief explicitly prohibits it. The check compared every hypothesis and clause with
the structure fields and theorem above. In particular: the local hull is not made
prorepresentable; square-zero kernels need not be principal; marked isomorphisms
retain the specified special fibre; the relative power-series map fixes all local
parameters; the stable implication is outside the no-derivations antecedent; and
the effective discriminant test includes all field-valued points and d=0.
