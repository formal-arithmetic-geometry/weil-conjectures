## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.TorusEndomorphismKernelDichotomy`
states `AlgebraicGeometry.torusEndomorphism_kernel_dichotomy`. Its sole theorem has
proof `sorry`, with the four-step DAG proof reproduced in its docstring. No definition
is introduced and no mathematical statement is corrected.

Clause-by-clause correspondence:

- The algebraically closed base field is `{F : Type u} [Field F] [IsAlgClosed F]`.
  The universe `u` is explicit and unrestricted.
- A group scheme over F is `T : Grp (Over (Spec (.of F)))`. The bundled group law
  is Mathlib's `GrpObj`, as prescribed by def-sc-group-scheme.
- The node defines a torus here as a group isomorphic over F to G_m^r. This is
  `hT : ∃ r : ℕ, Nonempty (T ≅ MultiplicativeType.splitTorus F r)`.
  The isomorphism is in group schemes, not merely in schemes or on F-points.
  The natural number includes zero. The already landed `splitTorus` is precisely
  the finite product of `StandardGroupSchemes.multiplicative F`, with the tensor
  unit in rank zero. Its owner def-sfb-tori-multiplicative-type was missing from
  the item's dependency list; it is added under the authorization to cite landed
  nodes. No duplicate notion or new node is needed.
- Affineness, finite type, smoothness and connectedness of these groups follow from
  being isomorphic to a finite product of G_m. Thus the existential split
  presentation already entails the standing affine finite-type context and no
  case is enlarged by omitting redundant structure assumptions. The node's
  explanation of maximal tori introduces no maximal-torus variable or assumption
  in this particular assertion.
- The arbitrary endomorphism of group schemes is `f : T ⟶ T`; its underlying
  scheme morphism is `f.hom.hom.left`.
- "Exactly one" is Mathlib's `Xor`, defined as `(P ∧ ¬ Q) ∨ (Q ∧ ¬ P)`;
  thus existence and exclusivity are both present.
- Case (i) is the conjunction `Flat f.hom.hom.left ∧ Surjective f.hom.hom.left ∧
  LocallyOfFinitePresentation f.hom.hom.left ∧ QuasiCompact f.hom.hom.left ∧
  QuasiSeparated f.hom.hom.left`. These are, in order, flatness, surjectivity
  of the underlying spectral map, local finite presentation, quasi-compactness,
  and quasi-separatedness. In particular finite presentation has not been
  replaced by local finite presentation alone.
- Case (ii) is an existential natural number `s`, a map
  `i : (MultiplicativeType.splitTorus F s).X ⟶ GrpObj.ker f.hom.hom`, and the
  conjunction `1 ≤ s ∧ IsClosedSubgroupScheme i`. The latter class includes
  that i is a homomorphism, injective on all algebra-valued points, and a closed
  immersion. This uses the actual kernel pullback, not the reduced kernel or
  just the kernel on geometric points. `GrpObj.kerRepresentableBy` identifies
  its A-points with the kernel of f_A. A split torus itself can be used as S:
  a closed inclusion of G_m^s is equivalent to a closed inclusion of some S
  together with S ≅ G_m^s. Composing i with `GrpObj.kerι` gives the requested
  closed subtorus of T; conversely any such subtorus killed by f factors through
  the kernel and is closed there, by the kernel pullback universal property.
- The positive-characteristic and trivial-torus sentences specify included cases,
  not separate additional conclusions. No characteristic-zero, separability,
  smooth-kernel, positive-rank-for-T or reduced-test-algebra assumption is present.

Dependency declarations read and used:

- def-weil-field: `Field` (Mathlib.Algebra.Field.Defs), the commutative division
  ring class; def-weil-algebraic-closure: `IsAlgClosed` from
  Mathlib.FieldTheory.IsAlgClosed.Basic, exposed through the recorded closure
  module and ToriMultiplicativeType. Its docstring identifies splitting with
  the node's root condition. No algebraic closure extension is chosen here.
- def-sc-group-scheme: `CategoryTheory.Grp`, `GrpObj` and `IsMonHom` in
  Mathlib.CategoryTheory.Monoidal.Grp / .Mon, and `GrpObj.ker` in
  WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp.
  The latter is the pullback of f and the unit; its `kerRepresentableBy` gives
  exactly the kernel on every test object's points.
- def-sc-group-scheme-subgroup: `AlgebraicGeometry.IsClosedSubgroupScheme` in
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs, extending
  IsSubgroupScheme and including IsClosedImmersion of the underlying map.
- def-sc-gm-ga: `StandardGroupSchemes.multiplicative` and its canonical
  `multiplicativeGroup` in Sheaf.AlgebraicGeometry.StandardGroupSchemes,
  the actual Laurent spectrum and Laurent Hopf group structure.
- Added landed dependency def-sfb-tori-multiplicative-type:
  `AlgebraicGeometry.MultiplicativeType.splitTorus` in
  Sheaf.AlgebraicGeometry.ToriMultiplicativeType. Its full recursive signature
  and docstring were read; the existing IsTorus predicate concerns splitting
  after algebraic closure, so the node's explicitly split presentation is
  stated using the same splitTorus construction directly.
- def-weil-flat-morphism: `Flat` in Mathlib.AlgebraicGeometry.Morphisms.Flat.
- def-sbc-locally-finite-presentation: `LocallyOfFinitePresentation` in
  Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation.
- def-weil-finite-type-morphism: `LocallyOfFiniteType` in
  Mathlib.AlgebraicGeometry.Morphisms.FiniteType and `QuasiCompact` in
  Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact. The latter is used in
  (i); the standing finite-type context is entailed by hT as described above.
- def-weil-quasi-separated-morphism: `QuasiSeparated` in
  Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated, quasi-compact diagonal.
- def-sbc-smooth-morphisms: `Smooth` in
  Mathlib.AlgebraicGeometry.Morphisms.Smooth, and def-weil-connected-scheme:
  `ConnectedSpace` in Mathlib.Topology.Connected.Basic. Their signatures and
  docstrings were read. They are contextual terminology, not additional
  hypotheses on an arbitrary kernel or the endomorphism in this node.

Statement imports are public; stated proof inputs are ordinary imports:
MultiplicativeCharacterAntiduality, GroupScheme.HomomorphismFactorization,
FreeModule.PID, FiniteDimensional.Lemmas, ClosedImmersion, Scheme, Separated,
and Flat.FaithfullyFlat.Algebra. Flat itself also supplies the affine criterion.
The two proof nodes lem-sfb-split-torus-hom-matrices and
lem-sfb-diagonalizable-group-geometric-criteria have no recorded Lean module
in the read base, so there is no module to import for them yet. They are not
needed to elaborate the statement and no dependency cycle is introduced.

Edge cases checked before writing:

- Rank zero: the split torus is the terminal group; its only endomorphism is an
  isomorphism, hence case (i), while a positive-rank closed subgroup cannot embed.
- Identity (any rank): case (i); the kernel is trivial.
- Trivial endomorphism in positive rank: case (ii), with the whole torus in its
  kernel; it is not surjective as a scheme morphism.
- Multiplication by p in characteristic p: its finite nonreduced kernel does not
  supply a positive-rank subtorus. The power map is finite faithfully flat and
  finitely presented, so case (i) includes it. No smoothness of f is asserted.
- Rank-deficient but non-diagonal integer exponent matrices: the character-map
  argument gives a positive-rank split kernel torus without assuming the matrix
  already has diagonal form.
- Nonreduced test algebras: the pullback kernel and closed-subgroup class retain
  all their points, including nilpotent structure.

Searches for an existing statement:

- msearch.py leanfinder: "An endomorphism of a split algebraic torus is faithfully
  flat or its kernel contains a positive dimensional subtorus" returned eight
  hits, including Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine and
  general faithfully-flat ring results, none giving this torus alternative.
- msearch.py loogle: `"torus", "ker"` returned zero hits.
- msearch.py grep: `[Tt]orus.*[Kk]ernel|[Kk]ernel.*[Tt]orus|[Tt]orus.*[Ff]lat`
  returned zero Mathlib hits.
- msearch.py leansearch: "An algebraic torus endomorphism is faithfully flat or
  has a positive dimensional torus in its scheme theoretic kernel" returned eight
  general flatness hits, none stating the alternative.
- rg of lean/WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json for
  `torusEndomorphism_kernel_dichotomy|torusEndomorphism|[Tt]orus.*[Dd]ichotomy`
  found only the reference to this item in BorelSchemeNormalizer's proof plan;
  no existing declaration. Searching splitTorus/IsTorus found the landed
  ToriMultiplicativeType construction, reused here. Searching the item's id in
  lean/WeilConjectures found no declaration; in lean/Sheaf it found the same
  BorelSchemeNormalizer proof-plan citation.

Source checked directly with pdftotext: Milne printed pp.232--234 (PDF pp.244--246),
Remark 12.5 and Theorem 12.9, including exactness of the character antiequivalence;
printed p.236 identifies split tori with free finite-rank character lattices.
No statement fault or STATEMENT-DISPUTED issue was found.

Validation: scompile.py Q62 lem-sfb-torus-endomorphism-kernel-dichotomy compiled
both the sandbox and library module modes successfully, about 1.8 seconds each,
with no errors or unexpected warnings. `set_option autoImplicit false` ensures
all variables and universes are explicitly bound. All lines are at most 100 columns.

## Second reading by Q62

The dispatcher forbids starting other agents; this section records a separate
self-check with the node and completed module open, not an independent worker
review. The maintainer supplies the independent review after delivery.

Re-read the field binders, bundled group scheme, existential split presentation
including r=0, arbitrary bundled endomorphism, all five properties of (i), and
positive rank plus a closed subgroup in the actual kernel in (ii). Each matches
the node as detailed above. In particular `Xor` supplies exclusivity, and
`IsClosedSubgroupScheme i` implies a closed inclusion into T after composition
with the closed kernel inclusion. No additional S, unrelated map, or pointwise
only condition has been substituted. The split presentation already forces the
standing affine finite-type assumptions. No additional smoothness or connectedness
of the kernel was introduced. The only metadata addition besides lean is the
already landed node owning splitTorus. The exact signature was extracted from the
completed file into lean.statement. No mismatch required a correction.
