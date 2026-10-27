## Worker report

The module `Sheaf.AlgebraicGeometry.SmoothDiagonalPrimeToTorsionDensity` states
`AlgebraicGeometry.smooth_diagonal_primeToTorsion_density`, with one `sorry` and no new
definitions. Its docstring records all six proof steps of the node, including the restricted
prime-to-characteristic multiples of the finite-factor order used for joint injectivity.
The node statement, proof, and proof dependencies are unchanged. `stmt_deps` gains the already
landed `def-sfb-diagonalizable-group`, whose exact canonical Hopf construction is used.

Hypotheses and objects, matched to the node:

- The algebraically closed field is `(F : Type u) [Field F] [IsAlgClosed F]`.
- The F-group scheme is `D : Grp (Over (Spec (.of F)))`. Affineness is
  `[IsAffine D.X.left]`; smoothness is `[Smooth D.X.hom]`; finite type is the pair
  `[LocallyOfFiniteType D.X.hom] [QuasiCompact D.X.hom]`.
- The finitely generated additive abelian group is `(M : Type u) [AddCommGroup M]
  [AddGroup.FG M]`. The group-scheme isomorphism is `e : D ≅ diagonalizableGroup F M`.
  The existing definition is the Hopf spectrum of `AddMonoidAlgebra F M`, with exactly
  the basis, product, comultiplication, counit and antipode written in the node.
  Supplying a chosen isomorphism instead of merely its existence does not restrict D.
- The characteristic exponent p is the existing `ringExpChar F`, defined as
  `max (ringChar F) 1`; for fields this is 1 in characteristic zero and char F otherwise.
- Each allowed integer is `n : ℕ` with `0 < n` and `n.Coprime (ringExpChar F)`.
- `D[n]` is the existing `torsionSubgroupScheme D.X n`, defined as
  `GrpObj.ker (𝟙 D.X ^ n)`, and its inclusion is `torsionSubgroupScheme.ι D.X n`.
  This is the actual kernel, not an arbitrary scheme or an assumed pointwise model.
  The upstream `torsionByPointsEquiv` identifies its points with those killed by n,
  and `isClosedSubgroupScheme_torsionSubgroupScheme_ι` identifies its inclusion as a
  closed subgroup for a commutative group. The given diagonalizable presentation
  entails commutativity; the statement does not add a commutativity assumption.

Conclusion clauses, matched to the node:

- For every allowed n, `∃ c : ℕ, 0 < c ∧ c.Coprime (ringExpChar F) ∧ ...` supplies
  the positive prime-to-p order c_n.
- `Nat.card (𝟙_ (Over (Spec (.of F))) ⟶ torsionSubgroupScheme D.X n) = c`
  identifies c with the number of rational points H_n. Positivity excludes the zero
  value that `Nat.card` assigns to an infinite type.
- `Nonempty (torsionSubgroupScheme D.X n ≅
  ∐ fun _ : Fin c ↦ 𝟙_ (Over (Spec (.of F))))` is the finite disjoint-union assertion.
  This is an isomorphism of F-schemes, and each terminal F-scheme is Spec F. Using c
  as the number of components is equivalent here to the separate point-count clause:
  over F, each copy of Spec F has exactly one rational point.
- The second conjunct quantifies over every `Z : Scheme.{u}` and every
  `i : Z ⟶ D.X.left` with `IsClosedImmersion i`. Its premise is exactly factorization
  of every allowed inclusion: an actual `j` satisfying
  `j ≫ i = (torsionSubgroupScheme.ι D.X n).left`. Its conclusion `IsIso i` says Z is
  the whole closed subscheme, including its scheme structure. No affineness or
  reducedness assumption is added on Z.
- The third conjunct quantifies over `f : AddMonoidAlgebra F M`. For each allowed n
  and each rational point x of D[n], compose x with the canonical inclusion and
  `e.hom.hom.hom.left : D.X.left ⟶ Spec F[M]`. `Spec.preimage` is the canonical
  evaluation homomorphism F[M] -> F. The premise says its value on f is zero for
  every x and n; the conclusion is `f = 0` in F[M].
- There is no connectedness assumption on D or M, and no connected-component reduction.

Existing dependency declarations read and reused:

- `Field`, `Mathlib.Algebra.Field.Defs` (through the public imports).
- `IsAlgClosed`, `Mathlib.FieldTheory.IsAlgClosed.Basic`; the dependency also records
  `AlgebraicClosure`/`IsAlgClosure`, but no choice of algebraic closure is needed here.
- `CategoryTheory.GrpObj`, `CategoryTheory.Grp`, `Mathlib.CategoryTheory.Monoidal.Grp`.
- `AlgebraicGeometry.IsSubgroupScheme`, `IsClosedSubgroupScheme`, the kernel and torsion
  constructions and their docstrings, `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`.
- `AlgebraicGeometry.Smooth`, `Mathlib.AlgebraicGeometry.Morphisms.Smooth`.
- `AlgebraicGeometry.LocallyOfFiniteType`, `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`;
  `AlgebraicGeometry.QuasiCompact`, `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`.
- `AlgebraicGeometry.Spec`, `Spec.map`, `Mathlib.AlgebraicGeometry.Scheme`;
  `Spec.preimage`, `Mathlib.AlgebraicGeometry.GammaSpecAdjunction` (reexported).
- `AlgebraicGeometry.IsClosedImmersion`,
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`.
- `AlgebraicGeometry.diagonalizableGroup`,
  `Sheaf.AlgebraicGeometry.DiagonalizableGroup`, now named in `stmt_deps`.

The proof-only imports are the recorded and available finite-abelian-group structure,
standard group schemes, CRT, affine coproducts (already public for the statement),
affine fibre products, tensor universal property, and monic quotient basis modules.
`lem-sfb-diagonalizable-group-geometric-criteria` and
`lem-sfb-split-binomial-root-torsor` do not yet have Lean declarations or modules in their
records, so there is no module to import for those proof dependencies.

Edge cases checked against the statement and the source:

- Characteristic zero uses p=1, so every positive n is included, without a false
  coprimality-to-zero condition. Positive characteristic excludes exactly its multiples.
- n=0 is excluded; n=1 is retained and has the identity kernel, c=1.
- M=0 and free rank zero are allowed, as are empty products in the proof.
- Nontrivial finite smooth factors are retained: mu_2 in characteristic 3 and
  G_m times mu_3 in characteristic 7 satisfy the hypotheses. In characteristic p,
  the nonsmooth mu_p is excluded by precisely the source's smoothness assumption.
- The group cannot be empty because of its identity section. The quantified Z may
  be empty, nonreduced, or otherwise arbitrary; factorization is the only premise.
- The site and scheme sizes use one explicit universe u, with M in that universe
  as in the published diagonalizable construction; the finite index Fin c imposes
  no restriction on u. No auto-bound variables, local notations or local instances.

Searches actually run:

- `msearch.py ... leanfinder "The prime to characteristic torsion kernels of a smooth
  diagonalizable group over an algebraically closed field are finite and schematically
  dense"`: 8 unrelated hits (AddCircle torsion and Ax-Grothendieck/model-theory results).
- `msearch.py ... loogle '"AddMonoidAlgebra", "IsReduced"'`: 0 hits.
- `msearch.py ... grep 'torsion.*(dense|Dense)|diagonalizable|schematicallyDense.*torsion'`:
  4 linear-algebra diagonalizability hits, no group-scheme theorem.
- `msearch.py ... leansearch "Smooth diagonalizable groups over algebraically closed
  fields have schematically dense prime to characteristic torsion"`: 8 hits concerning
  smoothness and smooth loci; none states this result.
- `rg` of `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for diagonalizable groups and torsion/density found the existing canonical
  `DiagonalizableGroup` module, the abelian and semiabelian density results, and other
  multiplicative-type results. None states the finite-kernel and density conjunction.
- Searching the exact item ID in `lean/WeilConjectures` returned no declaration;
  searching the new declaration name in Mathlib, WeilConjectures, Sheaf and the
  upstream-name index returned no clash.

Source read directly with pdftotext: Milne printed pp.231--233 (PDF pp.243--245),
including Proposition 12.3 and Remark 12.5, and printed pp.242--243 (PDF pp.254--255),
including Theorems 12.32 and 12.33. No statement correction or disputed statement.

Validation: `scompile.py Q08 lem-sfb-smooth-diagonal-prime-to-characteristic-torsion-density
<module>` compiled both its sandbox and its library-name form on the server in 1.7 seconds
per form, with no errors or warnings. The node's `lean.statement` is extracted verbatim
from the theorem signature; JSON uses indent 1, Unicode and a final newline.

## Second reading by Q08

I reopened the node and the final module for a separate second pass. This is a solo-worker
second pass, not a claim of review by another agent: the dispatcher explicitly forbids
starting other agents, and the independent maintainer review follows delivery.

The field, algebraic closedness, affine group, smoothness, both finite-type conditions,
finitely generated character group, and canonical group-scheme isomorphism each have the
binders listed above. The first conjunct has both the finite split scheme and the exact
positive prime-to-p rational-point count. The second conjunct quantifies all closed
subschemes and requires actual factorization of all allowed kernel inclusions; `IsIso i`
correctly retains scheme structure. The third conjunct evaluates functions through the
chosen diagonalizable presentation in the correct direction, from D to Spec F[M], and
concludes equality to zero in the actual group algebra. All three families use the same
positive, prime-to-p indices. There is no connectedness hypothesis, no assumed density,
and no arbitrary map replacing a canonical construction.

No mathematical mismatch was found in the second pass. The added dependency names the
existing diagonalizable definition rather than duplicating it. The upstream kernel
construction needs no extra typeclass assumption merely to form its scheme, so the final
signature correctly avoids adding a commutativity hypothesis just for an API instance.
