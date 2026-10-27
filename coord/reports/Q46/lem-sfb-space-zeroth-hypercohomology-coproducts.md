## Worker report

Stated `AlgebraicGeometry.AlgebraicSpace.zerothHypercohomology_coproduct_bijective`
in `Sheaf.AlgebraicGeometry.SpaceZerothHypercohomologyCoproducts`. The only new declaration
is this theorem, with proof `sorry`. No definition, additional assumption on cohomological
bounds, or Noetherian assumption is introduced. The statement of the DAG node is unchanged.

Clause-by-clause rendering:

- The size convention is rendered by explicit universes `u w v` and
  `set_option autoImplicit false`. `S : Scheme.{u}` is the base scheme, and
  `X : AlgebraicSpace S` is the already defined fppf-sheaf algebraic space.
- Quasi-compactness is `hqc : CompactSpace (Point X.obj.obj)`, for the existing point
  topology. Compactness means every open cover has a finite subcover.
- The **absolute** quasi-separatedness hypothesis is
  `hqs : X.IsAbsolutelyQuasiSeparated`. Its existing affine-test definition is precisely
  quasi-compactness of the absolute diagonal (Stacks 0AHR); it does not assume the base
  scheme quasi-separated. The change-of-base lemma is publicly imported as recorded.
- `X.DerivedModules` is the ambient unbounded derived category of module sheaves in the
  already landed small affine ringed model. `HasDerivedCategory.{w} X.SmallModules` fixes
  the localization morphism universe, rather than imposing a mathematical boundedness
  condition. `X.smallModuleEquivalence : X.Modules ≌ X.SmallModules` is the specified
  equivalence obtained by restriction to actual affine étale charts. This gives exactly
  the original ringed topos and module universe, not a new coefficient category.
- `I : Type v`, `E : I → X.DerivedModules`, and
  `hE : ∀ i : I, X.derivedQCohProperty (E i)` render every family in the full subcategory
  with quasi-coherent cohomology. The predicate applies the inverse of the recorded
  module equivalence to each cohomology sheaf and uses the recorded Mathlib
  `SheafOfModules.IsQuasicoherent` predicate. The family is not bounded in either direction.
- `c : Cofan E` and `hc : IsColimit c` specify an arbitrary ambient coproduct cofan. The
  ambient vertex is `c.pt` and its arrows are `c.inj i`. No coproduct is taken in QCoh,
  and quasi-coherence of the vertex is not an added hypothesis.
- `ringedSiteZerothHypercohomologyOfUniverses.{u,u,u,w}
  X.smallEtaleModelTopology X.smallStructureSheaf` is precisely the recorded
  `H⁰ RΓ`, with Γ = Hom(O,-), computed on K-injectives. Its target is AddCommGrpCat.{u}.
- `DirectSum.toAddMonoid (fun i ↦ (H.map (c.inj i)).hom)` is the requested homomorphism
  from the algebraic direct sum to H⁰ of the vertex. Mathlib's `toAddMonoid_of` gives
  its restriction to summand i as exactly `H.map (c.inj i)`. `Function.Bijective` asserts
  both injectivity and surjectivity. Classical decidable equality is explicitly scoped
  over the declaration, as in the compact-object example.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- Sheaf.AlgebraicGeometry.AlgebraicSpace: `AlgebraicGeometry.AlgebraicSpace`,
  `EtaleSite`, `structureSheaf`, `Modules`.
- Sheaf.AlgebraicGeometry.SpaceChangeBase: `exists_spaceChangeBase`, read with the complete
  section, restriction, atlas, equivalence and small-ringed-site signatures.
- Sheaf.CategoryTheory.RingedSiteModules: `CategoryTheory.ringedSiteModules`, transparently
  Mathlib's `SheafOfModules`.
- Mathlib.Algebra.Homology.DerivedCategory.Basic: `DerivedCategory`, `HasDerivedCategory`.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule: `QCoh`, and the exact
  underlying `SheafOfModules.IsQuasicoherent` predicate.
- Sheaf.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses:
  `CategoryTheory.ringedSiteZerothHypercohomologyOfUniverses`; its complete implementation
  is the right derived Hom-from-unit functor followed by zeroth homology.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel: `SmallModules`,
  `smallEtaleModelTopology`, `smallStructureSheaf`, `smallModuleEquivalence`.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules: `DerivedModules`,
  `derivedQCohProperty` (and the full-subcategory `DerivedQCoh`).
- Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated:
  `IsAbsolutelyQuasiSeparated`; Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology:
  `pointTopologicalSpace` on the existing `Point` classes.

The last four owning definition nodes were already landed; their IDs were added to
stmt_deps to record the exact public interfaces used. There are no new nodes, dependency
repairs, or statement corrections. Modules of all recorded proof dependencies are
imported privately; unstated proof dependencies have no module to import. Mathlib proof
leaves are imported from their recorded files. The complete six-step natural-language
proof is in the theorem docstring, including uniform truncation, the bounded-below
filtration comparison, naturality and the empty case.

Edge cases checked: I empty gives the initial ambient object and the zero-to-zero group
map; no Nonempty or finite-instance restriction excludes this. The empty algebraic space
has zero module cohomology. Zero summands are allowed. The family can have no common
lower bound: only quasi-coherent cohomology is assumed. A non-quasi-separated base does
not change the absolute diagonal predicate. The vertex is arbitrary subject only to its
specified coproduct universal property. Independent index and localization universes
are explicit, with no implicit equality of the original site's object and arrow levels.
The small affine model preserves the module section universe u.

Searches for an existing statement:

- msearch.py leanfinder: "zeroth hypercohomology preserves coproducts quasi compact quasi
  separated algebraic space": 8 hits, on affine global sections and finite coproducts;
  none is this unbounded algebraic-space statement.
- msearch.py loogle: "CategoryTheory.Functor.PreservesColimitsOfShape,
  DirectSum.toAddMonoid": 0 hits; the first name was reported unknown. Read the actual
  `DirectSum.toAddMonoid` and `toAddMonoid_of` declarations locally afterward.
- msearch.py leansearch: "zeroth hypercohomology commutes with direct sums on a quasi
  compact quasi separated algebraic space": 8 hits on zero hypercovers/direct-sum algebra;
  no match.
- msearch.py grep: "hypercohomology|Hypercohomology|preserves.*[Cc]oproduct" in
  Mathlib/Algebra/Homology: 2 unrelated monoidal finite-coproduct hits.
- rg in lean/WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json for the node ID,
  zerothHypercohomology, zeroth_hypercohomology, hypercohomology with coproducts/direct sums,
  and the proposed declaration name: found existing functors and related countability,
  amplitude and generator statements, but no declaration stating this result. Read the
  small-model and countable-hypercohomology consumers to follow the established API.

Source read: literature/stacks-project/spaces-perfect.tex, lines around
lemma-quasi-coherence-pushforward-direct-sums (08FB), and the first paragraph of
proposition-compact-is-perfect (09M8). The former uses uniform truncation and the
bounded-below spectral sequence; the latter explicitly invokes precisely H⁰ coproduct
preservation for a qcqs algebraic space.

Validation: prescribed scompile.py, sandbox and final library-module mode, both clean
(10.5 s and 10.3 s). No theorem was proved in this stage-2 delivery. No statement dispute.

## Second reading by Q46

The dispatcher explicitly prohibits starting other agents; no independent group reader
was created. This section records a separate self-check against the opened node and final
Lean file; the maintainer's independent review remains the independent reading.

Rechecked every binder and conclusion: arbitrary base scheme and algebraic space; actual
point-space compactness; absolute affine-test quasi-separatedness, including a bad base;
the recorded equivalent ringed model and arbitrary localization universe; unbounded
quasi-coherent family; arbitrary ambient Cofan with IsColimit; and bijectivity of the
DirectSum.toAddMonoid comparison induced by the exact H⁰ functor on every c.inj. The
canonical summand identity follows from the existing `DirectSum.toAddMonoid_of` and is
not an extra theorem or axiom. No upper/lower bounds, Noetherian condition, separate
quasi-coherence assumption on c.pt, or nonempty restriction appeared. No mismatch was
found. The explicit stmt_deps additions document already landed notions used in the
signature and preserve the mathematical statement and accepted proof plan.
