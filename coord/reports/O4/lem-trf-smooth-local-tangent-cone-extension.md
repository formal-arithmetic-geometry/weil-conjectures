## Worker report

Module: `Sheaf.RingTheory.SmoothLocalTangentConeExtension`.
Main declaration: `Algebra.smooth_local_tangent_cone_extension`.
This is a statement-only delivery with one postponed theorem and one real scalar-action
instance. The item's node changes only in `lean`. No statement correction, new node,
or dependency-node repair is needed.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The two commutative local rings are `{A : Type u} {B : Type v}`, `[CommRing A]`,
  `[CommRing B]`, `[IsLocalRing A]`, and `[IsLocalRing B]`. Mathlib's `IsLocalRing`
  extends `Nontrivial`, so these explicitly retain the node's nonzero requirement.
  The independent universes `u v` impose no equality of sizes.
- The rational-algebra structures are `[Algebra ℚ A] [Algebra ℚ B]`.
  The hypotheses `[EssFiniteType ℚ A] [EssFiniteType ℚ B]` are precisely
  localizations of finite-type rational algebras, not finite type themselves.
- The given map is `algebraMap A B` from `[Algebra A B]`. Every ring homomorphism
  between commutative rings supplies this algebra structure. Its locality is
  `[IsLocalHom (algebraMap A B)]`. No compatibility restriction on rational actions
  is added: a unital ring map between rational algebras necessarily preserves rationals.
- `hsmooth : EssentiallySmooth A B` uses the dependency's localization-of-smooth-algebra
  predicate, not the potentially stronger predicate `Smooth A B`.
- The ideals m and n are the actual `IsLocalRing.maximalIdeal A` and
  `IsLocalRing.maximalIdeal B`. Their residue fields K and L are Mathlib's
  `IsLocalRing.ResidueField A` and `IsLocalRing.ResidueField B`.
- The closed fibre F is written out as
  `B ⧸ (IsLocalRing.maximalIdeal A).map (algebraMap A B)`.
  The first conjunct is `IsRegularLocalRing` of exactly this ring, including its
  Noetherian and local properties. There is no separate regularity assumption.
- `∃ s : ℕ, ringKrullDim F = (s : WithBot ℕ∞) ∧ ...` introduces the node's
  `s = dim F` without taking a truncated natural dimension that could hide an
  infinite or negative dimension. Its finiteness is a conclusion, not a hypothesis.
- The `e` is an `L`-algebra equivalence from
  `MvPolynomial (Fin s) (L ⊗[K] Ideal.associatedGraded m)` to
  `Ideal.associatedGraded n`, the inverse orientation of the displayed isomorphism.
  The residue-field extension algebra structure is Mathlib's canonical instance
  for local algebra maps (`LocalRing/ResidueField/Basic.lean`, section
  `FiniteDimensional`), induced by the actual map A to B.
- The first condition on `e` quantifies over every degree `d`, exponent vector `b`,
  scalar `c : L`, and class `x : m^d/m^(d+1)`. It requires
  `e (monomial b (c ⊗ ι_d x)) = ι_(d+b.degree) y` for some class `y`.
  Thus polynomial variables have degree one, residue-field scalars degree zero,
  and the coefficient grading is retained. These homogeneous pure-tensor monomials
  span each homogeneous component; this condition is exactly preservation of the
  total grading. The canonical tensor grading exists because extension of fields
  is flat (indeed the direct-sum splitting also supplies its decomposition).
  An injective and surjective linear map between these direct sums that preserves
  each degree has degree-preserving inverse: decompose a preimage into degrees;
  all other components have zero image and vanish by injectivity.
- The second condition on `e` quantifies over every `a ∈ m^d`. Its witness
  `b ∈ n^d` satisfies `b.val = algebraMap A B a.val`, and it requires
  `e (C (1 ⊗ ι_d [a])) = ι_d [b]`. The subtype witness has a fixed value,
  so this does not quantify over an arbitrary comparison map or arbitrary image.
  Quotient surjectivity and additivity fix the restriction on the whole base
  graded algebra; L-linearity fixes its scalar extension. This states exactly
  the required restriction, rather than merely an ungraded algebra isomorphism.
- The final equality is between sets in `WithBot ℕ∞`, using
  `q ∈ minimalPrimes B` and `p ∈ minimalPrimes A` and the actual quotient-ring
  dimensions. The right-hand side adds `(s : WithBot ℕ∞)` to each dimension.
  This is equality of sets of dimensions, with neither a minimal-prime bijection
  nor an identification of the residue fields imposed.

Dependency declarations read and used:

- `Mathlib.RingTheory.EssentialFiniteness`, `Algebra.EssFiniteType`, from the
  mathlib-only record of def-weil-pbc-essentially-finite-type-algebra. Its docstring
  and class definition give localization of a finite-type algebra.
- `WeilConjectures.RingTheory.EssentiallySmooth`, `Algebra.EssentiallySmooth`:
  the full existential localization definition, including its universe convention.
- `Mathlib.RingTheory.KrullDimension.Basic`, `ringKrullDim`: dimension in
  `WithBot ℕ∞`, as recorded by def-weil-pbc-krull-dimension-ring.
- `Mathlib.RingTheory.RegularLocalRing.Defs`, `IsRegularLocalRing`, the ring clause
  of def-weil-regular-scheme's retained `mathlib_match`. The node explicitly says
  this match continues to supply its unchanged ring notions; its scheme declaration
  `AlgebraicGeometry.IsRegularScheme` in `Sheaf.AlgebraicGeometry.IsRegularScheme`
  was read but is not needed for this ring-only statement.
- `WeilConjectures.RingTheory.AssociatedGradedRing`, `Ideal.associatedGraded`,
  `Ideal.associatedGradedPiece`, and `Ideal.associatedGradedAlgebra`. The full
  construction and docstrings were read: these are exactly the ideal-power
  quotients, their direct sum, and the degree-zero quotient scalar action.

The public helper `IsLocalRing.associatedGradedAlgebra` is only a definitionally
identical instance transport: `inferInstanceAs (Algebra (A ⧸ maximalIdeal A) ...)`.
Mathlib defines `ResidueField A` as that quotient, but instance search would not
unfold this wrapper to find `Ideal.associatedGradedAlgebra`. The helper has no
postponed data or proof, introduces no second associated graded object or action,
and is listed in `lean.declarations`.

The source passages of Stacks `algebra.tex` were read locally: Tag 00T7,
`lemma-standard-smooth`, and Tag 00ON, `lemma-dimension-base-fibre-equals-total`.
Neither is misrepresented as the complete tangent-cone theorem. The module
attributes the coefficient-compatible presentation and finite-jet argument to
the node's actual proof. Its docstring reproduces all nine proof steps and names
their supporting nodes. All recorded proof-dependency modules are imported privately
when present, and Mathlib matches likewise. The proof-only node
`lem-trf-relative-cohen-flat-presentation` has no recorded declaration and hence
no module to import; it is named explicitly in the proof docstring. The item does
not need its completion objects in its signature, so no premature statement of
that proof prerequisite is necessary.

Edge cases checked before writing:

- Identity local map: F is the residue field and s is zero; `Fin 0` gives the
  polynomial algebra with no variables, and the restriction is the identity.
- Extension of fields: both maximal ideals are zero and s is zero, while K and L
  may differ; the tensor product and canonical residue-field algebra retain this.
- A field mapping to a smooth local polynomial algebra of positive dimension:
  the degree-one variable condition is present, and the dimension shift is s.
- The smooth local algebra at a nonclosed point, such as the generic point of an
  affine line over a field, has fibre local-ring dimension zero despite positive
  relative topological dimension. The statement uses `ringKrullDim F`, not the
  relative rank of differentials, so this case is retained.
- Nonreduced and nonequidimensional rational local base rings are not excluded:
  no domain, reducedness, equidimensionality or regularity hypotheses are added.
- The zero rings are excluded precisely by the source's nonzero local condition.
  Degrees d = 0, empty variable sets, and zero homogeneous elements remain allowed.

Searches for existing statements and notions (2026-10-22):

- `msearch.py ... leanfinder "essentially smooth local ring extension associated
  graded tangent cone polynomial algebra residue fields"`: 8 hits, including
  `Algebra.IsSmoothAt`, `Algebra.IsStandardSmooth`, `Algebra.Smooth`, and smooth
  charts; none states this tangent-cone and minimal-component result.
- `msearch.py ... leansearch "An essentially smooth local ring map induces an
  isomorphism of the tangent cone with a polynomial ring over the residue field
  base change"`: 8 hits, including `RingHom.FormallySmooth`,
  `Algebra.FormallySmooth.iff_injective_lTensor_residueField`, smoothness predicates,
  and standard-smooth base change; no equivalent theorem.
- `msearch.py ... loogle '"associatedGraded", "Smooth"'`: no hits.
- `msearch.py ... grep 'associatedGraded|graded.*[Ss]mooth|[Ss]mooth.*graded'
  RingTheory`: no hits in Mathlib.
- `rg` in `lean/WeilConjectures/RingTheory` and `lean/Sheaf/RingTheory` for
  `associatedGraded|smooth_local_tangent|tangentCone`, followed by project-wide
  searches for graded maps/base change: found the existing associated-graded
  construction and the formally-etale and regular-sequence comparison files,
  none of which states the present essentially-smooth theorem.
- Literal item-id search in `lean/WeilConjectures`: no declaration.
- `rg` for `associatedGradedAlgebra|smooth_local_tangent_cone_extension` in
  `lean/Sheaf`, `lean/WeilConjectures`, and `dag/lean_names_upstream.json`:
  only `Ideal.associatedGradedAlgebra` was already present; the transported
  `IsLocalRing` instance and main theorem names were unused.
- `tools/blueprint_refs.py ancestor` confirms the ancestor
  `lem-trf-local-term-locality`. No new definition node is necessary.

There is no STATEMENT-DISPUTED issue and no change to the natural-language statement.
Validation: the prescribed `scompile.py` compiled the completed module cleanly
in both its scratch and owning-module contexts. The first diagnostic was the
residue-field scalar-action instance-search issue described above and was repaired.

## Second reading by O4

A second pass read the original node and completed Lean side by side. The local,
nonzero, rational-algebra, essentially-finite-type and essentially-smooth hypotheses
are all present, with no smoothness assumption on the local algebra itself. The
closed fibre is the quotient by the mapped base maximal ideal. Its regular-local
property and finite natural dimension are conclusions. The equivalence is over L,
uses the actual residue-field map K to L, preserves every total homogeneous degree,
and its restriction sends each base representative to its image under the given
map. The final equality is of dimension sets rather than a prime correspondence.
The existential natural s does not truncate an infinite dimension: its equality
with `ringKrullDim F` is asserted explicitly. No counterexample or mismatch was
found in the identity, unequal-residue-field, zero-dimensional-fibre, nonreduced,
or nonequidimensional cases. The sole elaboration repair was to expose the
existing quotient action through the definition of the residue field; no hypothesis
or conclusion was altered. This was a self-review pass; the maintainer's delivery
review is independent, as required by the dispatcher's no-subagent instruction.
