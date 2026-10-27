## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.InducedWeylDimensionFormula` states
`AlgebraicGeometry.induced_weyl_dimension_formula`, with its sole proof `sorry`.
It introduces no definitions or helper theorems. The node's statement is unchanged.

Sources read: the item's complete statement and four proof steps; all statement
dependency node statements and their recorded declarations, signatures and docstrings;
Milne, Algebraic Groups (2017), printed pp.479--480 (PDF pp.491--492), Definition
22.21 on printed p.468, and the latest blueprint
`sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` and its direct-images
proof, clause (3). The numerical input lies below the inherited Haboush/Steinberg
prerequisite, not in the unit statement. Jantzen is not local, as the node records.
Milne's signs and his unrestricted simple-module claim in 22.52 have already been
corrected in this node's accepted stage-1 split; this statement follows that split.

Hypotheses and clauses, matched to the Lean statement:

- Algebraically closed field: `{F : Type u} [Field F] [IsAlgClosed F]`. No
  characteristic hypothesis is present.
- Group scheme: `G : Grp (Over (Spec (.of F)))`. `hG : IsSemisimpleGroupScheme G.X`
  is the recorded predicate, whose definition spells out smoothness, connectedness,
  affineness, finite type, and absence of nontrivial smooth connected solvable normal
  closed subgroup schemes. Solvability uses its scheme-theoretic commutator series.
- Simply connected: `hsc` quantifies over every semisimple source `G'` and every
  homomorphism `f` with surjective underlying scheme morphism and finite kernel.
  Its further premise states that kernel points commute with every source point
  over every commutative F-algebra; the conclusion is `IsIso f`. This is exactly
  the interface of `exists_rho_section_modules` and the character-lattice theorem.
- The fixed torus and Borel: `T B`, maps `iT iB j`, and `hT`, `hsplit`, `hB`, `hj`
  specify the split maximal torus, Borel subgroup and compatible inclusions.
  The commutative-group witnesses are those exposed by the Borel-pair theorem;
  they only provide the additive character/cocharacter Hom-group structures.
- Actual character lattice: `Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))`.
  Cocharacters use the reverse Hom group. The finite set `Φ`, `RootDatum P` and
  its `Base b` use the exact interface of the recorded Borel-pair theorem.
- `aG`, `aB`, `haG`, `haB` pin the tangent actions to conjugation by the given
  torus inclusions. `hroot` identifies roots with the actual characters; `hpair`
  identifies the integer pairing with composition equal to the integer power map.
  `hweights` says exactly that the roots are all nonzero character weights in Lie(G).
  `hpositive` identifies positive roots with the weights occurring in Lie(B).
  These are character weights, including in characteristic p, not their differentials.
- The projection is `p : B ⟶ T` with `hp : j ≫ p = 𝟙 T`. In this split Borel
  setting this characterizes the projection of the dependency: a homomorphism
  from the smooth connected unipotent radical to a torus is trivial, so every
  such retraction kills the radical and the semidirect-product decomposition
  determines it uniquely. Thus the binder does not substitute an arbitrary map
  for the canonical projection. It includes every projection supplied by the
  recorded Borel-pair theorem, without adding a condition on G or the Borel.
- The integral half sum is `ρ` with `hρ : 2 • ρ = ∑ α : Φ with b.IsPos α, P.root α`.
  This is an equality in the actual character lattice, not a division in F.
- The weight is `lam` (Lean reserves the token lambda). `hlam` requires
  `0 ≤ P.toLinearMap lam (P.coroot α)` for every `α : b.support`, exactly dominance
  on the simple coroots. The extension is literally `p ≫ lam.toMul`.
- The actual function module is the already-defined
  `RhoSection.sectionModule G B iB (p ≫ lam.toMul) 1`. Its definition intersects
  kernels of the equations `f(gb) - characterValue(b)^1 * f(g) = 0` over all
  commutative F-algebras, including nonreduced algebras. The exponent one ensures
  the positive right-semi-invariance equation in the item, namely E_B(-lambda).
- Finite dimensionality is the first conclusion, `Module.Finite F (...)`.
  `RhoSection.HasRationalLeftTranslation G (...)` states the specified rational
  left action, whose columns are evaluated by `f(s⁻¹g)` on every algebra.
  It neither replaces the function subspace nor changes the action.
- Each denominator is a positive integer: the next conjunct states
  `0 < P.toLinearMap ρ (P.coroot α)` for every positive root. The codomain here is ℤ.
- The last conjunct equates `Module.finrank F (...)`, cast to ℚ, to the finite
  product of `(P.toLinearMap (lam + ρ) (P.coroot α) : ℚ)` divided by
  `(P.toLinearMap ρ (P.coroot α) : ℚ)`, over exactly the positive roots.
  Thus the dimension is an ordinary natural number and every ratio and the entire
  product are in ℚ, including in positive characteristic.
- The empty-root convention is built into the finite product: for `Φ = ∅`, it
  is one. There is no nonempty-root or positive-rank premise.
- The node's descriptions of arbitrary rational modules, simple modules,
  highest-weight lines and U-invariants explain terminology; the assertion
  quantifies over no such V, and imposes no simplicity hypothesis or conclusion.

Dependency declarations used:

- Mathlib `Field` (`Algebra/Field/Defs.lean`, definition and docstring read) and
  `IsAlgClosed` (`FieldTheory/IsAlgClosed/Basic.lean`, definition and equivalence
  with root existence read) render the first two Mathlib leaves.
- `CategoryTheory.Grp`, `GrpObj`, `IsMonHom`, `IsCommMonObj`, `GrpObj.ker`,
  `GrpObj.kerι` and `AlgebraicGeometry.IsFinite`: the group-scheme node's recorded
  interfaces, read in Mathlib and `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`.
- `Sheaf.AlgebraicGeometry.RhoSectionModules`: `IsRhoBorelPair` and
  `exists_rho_section_modules`; the theorem's simply-connected binders and its
  split Borel-pair interface are used. Its public module
  `Sheaf.AlgebraicGeometry.RhoSectionModuleData` provides `RhoSection.sectionModule`,
  `Coordinate`, `evaluate`, `characterValue` and `HasRationalLeftTranslation`;
  their full definitions and docstrings were read.
- `Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure`:
  `reductive_borel_pair_structure` and `semisimpleGroupScheme_isReductive`; its
  actual root/character/cocharacter/base and pinned-action interface is used.
- Stated proof dependencies imported without `public`:
  `Sheaf.AlgebraicGeometry.GroupScheme.HomogeneousLineBundleSections`
  (`exists_homogeneousLineBundle_sections`),
  `Sheaf.AlgebraicGeometry.GroupScheme.SimplyConnectedCharacterLattice`
  (`simplyConnected_character_lattice`), and
  `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex`
  (`Scheme.Modules.finite_sections_higherDirectImage`, and the recorded coherence
  theorem). Their source signatures and proof docstrings were read.
- The three proof dependencies Kempf vanishing, flag-line Euler alternant, and
  Weyl-alternant augmentation have no Lean record on the inspected base, so no
  invented module imports were added. Their mathematical uses remain explicit
  in the theorem's four-step proof docstring.

Edge cases checked before writing: in rank zero the character lattice of the
semisimple group is zero, the module is constants, the product is 1 and denominator
positivity is vacuous. For SL2 and weight n times its fundamental weight, rho is
the fundamental weight and the formula gives n+1, including n=0. For n=p in
characteristic p it still gives p+1 as an ordinary dimension; the module need not
be simple. The equation defining rho does not divide by 2 in characteristic 2.
The zero weight gives product 1 in every rank. All algebra tests in the reused
interfaces are in the field/scheme universe u, rather than an unrelated smaller
universe, and no reducedness assumption is imposed on the test algebras.

Searches performed in this session:

1. `msearch.py leanfinder`, query `Weyl dimension formula for dominant rational
   induced algebraic group modules in every characteristic`: 8 hits, including
   `LieModule.zero_lt_finrank_genWeightSpace`, `LieModule.rank`, `FDRep.char_one`,
   trace/generalized-weight-space facts, and an sl2 primitive-vector lemma.
   Their returned types concern Lie modules or ordinary monoid representations;
   none states this function-space dimension formula.
2. `msearch.py loogle`, query `"weyl", "finrank"`: zero hits.
3. `msearch.py leansearch`, query `Weyl dimension formula for the space of regular
   functions with prescribed Borel semi invariance`: 8 hits about weighted
   polynomials, Lie weights, root orbits and invariant forms, no exact match.
4. `msearch.py grep`, query
   `Weyl.*dimension|weyl.*finrank|induced.*dimension|dimension.*induced`: three
   unrelated hits in spectral norms and topological finite-dimensional modules.
5. Direct `rg -n` over both `lean/WeilConjectures` and `lean/Sheaf`, query
   `induced.*[Dd]imension|[Ww]eyl.*[Dd]imension|induced_weyl_dimension|lem-sfb-induced-weyl-dimension-formula`:
   five unrelated hits (finite-group induction, geometry and Koszul modules),
   no existing statement or declaration-name collision.
6. Read the existing notion definitions and full dependency sources listed above.
   The required semi-invariant function space and rational left action exist, so
   no duplicate definition, new node or dependency repair was needed.

No statement dispute or node correction is needed. The file sets `autoImplicit false`,
binds universe u explicitly, has lines at most 100 characters, and proves nothing.

## Second reading by Q48

The dispatcher brief assigns the independent review to the maintainer and prohibits
starting other agents. This is a second pass by the same worker, not a claim of an
independent reader. I reread the node and the final file together. Checked the actual
right-semi-invariance sign against `sectionModule` and the inverse fibre character;
the left action against `HasRationalLeftTranslation`; every group-theoretic premise
against the dependency signatures; actual character roots and coroots against
`hroot`, `hpair`, `hweights`, `hpositive`; dominance against `b.support`; and all
three numerical clauses against the final conjunction. No mathematical mismatch
was found. The first compile required renaming the reserved binder `λ` to `lam`;
the final node signature was extracted verbatim after that change. The empty-root,
zero-weight and positive-characteristic checks above were repeated.

Validation: the required `scompile.py Q48 lem-sfb-induced-weyl-dimension-formula`
completed with exit 0 for both the sandbox and final library module, with no
compiler diagnostics. A final direct search of `dag/lean_names_upstream.json` and
Mathlib found no collision for `induced_weyl_dimension_formula`. The JSON comparison
confirmed that `lean` is the only changed node field; its signature is verbatim.
