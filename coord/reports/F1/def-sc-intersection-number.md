## Worker report

The module `Sheaf.AlgebraicGeometry.IntersectionNumber` defines
`AlgebraicGeometry.Scheme.Modules.intersectionNumber` as a rational polynomial coefficient,
and `selfIntersectionNumber` as the repeated-line-bundle abbreviation. There are no theorems
and no sorries. The node is unchanged except for its `lean` record.

Clause-by-clause correspondence:

- A field k is `(k : Type u) [Field k]`.
- X proper over k is `(X : Scheme.{u}) [X.Over (Spec (.of k))]`
  and `[IsProper (X ↘ Spec (.of k))]`, with the project's prescribed over-base encoding.
- The closed immersion is `(Z : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i]`.
- Nonempty Z is `[Nonempty Z]`.
- Its dimension d is `(d : ℕ)` and the proof binder
  `_hd : topologicalKrullDim Z = ((d : ℕ∞) : WithBot ℕ∞)`.
- The d invertible modules are `L : Fin d → X.Modules` with
  `[∀ j : Fin d, (L j).IsInvertible]`.
- The structure sheaf O_Z is `𝟙_ Z.Modules`; its direct image is
  `(pushforward i).obj (𝟙_ Z.Modules)`.
- Integer exponents are `n : Fin d → ℤ`. Nonnegative exponents use
  `(L j).tensorPow (n j).toNat`; negative exponents use
  `(L j).dual.tensorPow (-n j).toNat`, just as in the dependency's recorded statement.
- The successive tensor products are the `List.ofFn` fold, starting with i_* O_Z.
- Euler characteristic is the recorded `eulerChar k`, cast into ℚ to match evaluation
  of the rational numerical polynomial.
- The polynomial is selected by `Classical.epsilon` with the predicate that every integer
  lattice evaluation is the specified Euler characteristic. This is genuine data specified
  by a predicate, not data supplied by sorry. Snapper applied to coherent i_* O_Z gives
  existence; polynomial identity over the infinite integer subset of ℚ gives uniqueness.
  Consequently any polynomial selected by this predicate is exactly the node's polynomial.
  No coherence or polynomial witness is added as an input hypothesis.
- The coefficient is `MvPolynomial.coeff` at the Finsupp whose exponent at every Fin d
  index is 1, constructed with `Finsupp.onFinset Finset.univ`.
- The total degree bound and the identification of the support dimension with d are
  supplied mathematically by the cited Snapper lemma and the closed immersion; as the node
  expressly says, these assertions are not part of this definition.
- The repeated-module convention is `selfIntersectionNumber`, calling `intersectionNumber`
  on `fun _ : Fin d => L`. The value is rational because the definition is a coefficient
  of a rational numerical polynomial. Its integrality is a property, not extra input data.

Dependency declarations read and used:

- `Field`, Mathlib.Algebra.Field.Defs: nontrivial commutative division ring.
- `AlgebraicGeometry.IsProper`, Mathlib.AlgebraicGeometry.Morphisms.Proper: separated,
  universally closed, locally finite type; universal closedness supplies quasi-compactness.
- `AlgebraicGeometry.IsClosedImmersion`, Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion:
  closed embedding and surjective stalk maps.
- `topologicalKrullDim`, Mathlib.Topology.KrullDimension: dimension in WithBot ℕ∞.
- `AlgebraicGeometry.Scheme.Modules.IsInvertible`,
  WeilConjectures.AlgebraicGeometry.Modules.Invertible: locally the structure sheaf.
  The same module supplies `tensorPow` and the monoidal structure.
- `AlgebraicGeometry.Scheme.Modules.eulerChar`,
  WeilConjectures.AlgebraicGeometry.Cohomology.Defs: alternating finsum of cohomology dimensions.
- `AlgebraicGeometry.Scheme.Modules.exists_mvPolynomial_eulerChar_tensorPowers`,
  Sheaf.AlgebraicGeometry.SnapperNumericalPolynomial: existence of the rational polynomial
  with these integer-lattice evaluations. Its module is imported; its theorem is the
  external justification of the selection, not a further result proved in this file.
- `AlgebraicGeometry.Scheme.Modules.pushforward`, Mathlib.AlgebraicGeometry.Modules.Sheaf:
  direct image of modules using the structure morphism's map of rings.

Edge cases: d=0 is allowed, with empty Fin 0, empty tensor-factor list, and exponent
vector 0; this extracts the constant coefficient χ(X,i_*O_Z). Negative exponents use the
invertible dual; exponent 0 uses the tensor unit. All characteristics are allowed. No
reducedness, integrality, smoothness, or ampleness is assumed. Empty Z is explicitly excluded
by the node; infinite dimension cannot equal the given finite d. All universes and variables
are bound explicitly, with k, X and Z in the common scheme universe of the existing dependency.

Searches performed (2026-10-11 UTC):

- msearch.py leanfinder: "intersection number of line bundles on a proper scheme as coefficient
  of multivariate Euler characteristic polynomial": 8 hits concerning ideal sheaves,
  intersections of opens, and projective spectra, none defining intersection numbers.
- msearch.py loogle: "MvPolynomial.coeff, Scheme.Modules.eulerChar": 0 hits, unknown identifier
  MvPolynomial.coeff in the service. Local source inspection confirms the coefficient API.
- msearch.py grep: "intersectionNumber|intersection_number|intersection number" in
  Mathlib/AlgebraicGeometry: 0 hits.
- msearch.py leansearch: "intersection number line bundles coefficient Euler characteristic
  polynomial": service unavailable, Internal Server Error.
- rg with the same intersection-number names and `def-sc-intersection-number` in
  WeilConjectures and lean/Sheaf: no hits. Thus neither project already defines this notion.

Source: local literature files are not present on this machine. Read the official Stacks
Definition 33.45.3 at https://stacks.math.columbia.edu/tag/0BEP; its coefficient definition
and repeated-module convention agree with the node. No node fault or STATEMENT-DISPUTED issue.

Additional name checks: `rg` in `dag/lean_names_upstream.json` found no matching declaration;
`grep -rn def-sc-intersection-number` in WeilConjectures found no node annotation.
The coefficient declaration was read in Mathlib/Algebra/MvPolynomial/Basic.lean, line 513.
Server single-file compilation passed cleanly in 1.8 seconds.

## Second reading by F1

Read independently against the sandbox node, the base node, every statement dependency's
node and recorded declaration, and the delivered module. The local literature checkout
is absent. Retrieved the Stacks varieties.tex source from the official stacks/stacks-project
repository into scratchpad/varieties.tex and read section-num (lines 10185 onwards),
lemma-numerical-polynomial-from-euler, and definition-intersection-number (lines 10389
onwards). Also checked [Tag 0BEP](https://stacks.math.columbia.edu/tag/0BEP) and
[Section 0BEL](https://stacks.math.columbia.edu/tag/0BEL). The section adds no standing
hypotheses beyond the field, proper scheme, and coherent modules used for polynomiality.
The source's second Euler-characteristic expression is a projection-formula identity;
the node intentionally defines the number using the first expression and does not claim
that identity as another clause. This agrees with the source definition.

Object/hypothesis/conclusion inventory and correspondence (H3):

1. Field k: `(k : Type u) [Field k]`. Read Mathlib.Algebra.Field.Defs `Field`, extending
   CommRing and DivisionRing. Verdict: exact; no characteristic restriction.
2. Scheme X over k: `(X : Scheme.{u}) [X.Over (Spec (.of k))]`. Its structure morphism is
   `X ↘ Spec (.of k)`, the prescribed scheme-over-base encoding. Verdict: exact.
3. Properness: `[IsProper (X ↘ Spec (.of k))]`. Read Mathlib.Morphisms.Proper:
   separated, universally closed, locally of finite type. Universal closedness provides
   quasi-compactness, hence finite type. Verdict: exact; no extra projectivity, smoothness,
   reducedness, or integrality.
4. Closed subscheme Z and embedding i: `(Z : Scheme.{u}) (i : Z ⟶ X)
   [IsClosedImmersion i]`. Read the Mathlib class: closed embedding of spaces and
   surjective stalk maps. Verdict: the recorded dependency's closed immersion, not a
   mere closed subset or arbitrary morphism.
5. Nonempty Z: `[Nonempty Z]`. Verdict: explicitly required by the node, present exactly.
6. Dimension d: `(d : ℕ)` and
   `(_hd : topologicalKrullDim Z = ((d : ℕ∞) : WithBot ℕ∞))`.
   Read topologicalKrullDim: Order.krullDim of IrreducibleCloseds. Verdict: correct
   finite topological dimension, not dimension of X. The proof is retained as an input
   although coefficient extraction itself does not depend on its proof term.
7. d invertible modules on X: `(L : Fin d → X.Modules)
   [∀ j : Fin d, (L j).IsInvertible]`. Read the recorded upstream IsInvertible:
   locally isomorphic to the structure sheaf. Verdict: exact finite tuple; no ampleness
   or arbitrary unlinked inverse object.
8. Structure sheaf on Z and direct image: `(pushforward i).obj (𝟙_ Z.Modules)`.
   Read the upstream MonoidalCategory instance: tensor product over O_Z with unit O_Z;
   read Mathlib pushforward: SheafOfModules.pushforward of i.toRingCatSheafHom.
   Verdict: i_*O_Z, not an inverse image or constant sheaf.
9. Integer tensor powers and tensor product with i_*O_Z: `n : Fin d → ℤ`,
   `if 0 ≤ n j then (L j).tensorPow (n j).toNat else
   (L j).dual.tensorPow (-n j).toNat`, followed by List.ofFn and foldl with `(M ⊗ N)`.
   Read tensorPow (zero is unit; successor tensors with L) and dual
   (`homObj M (SheafOfModules.unit _)`). Verdict: correct positive, zero, and negative
   powers and factor order; this is exactly the recorded Snapper encoding.
10. Euler characteristic: the folded module's `.eulerChar k`, cast to ℚ.
    Read upstream Cohomology.Defs: alternating finsum of finrankH, with cohomology
    carrying its k-vector-space structure from the same scheme-over-k instance.
    Verdict: the node's recorded notion. Properness and coherence of these twists give
    finite-dimensional cohomology and finite support, so the finsum has its intended
    meaning; these are consequences, not additional input hypotheses.
11. Representing numerical polynomial: `Classical.epsilon fun P :
    MvPolynomial (Fin d) ℚ => ∀ n : Fin d → ℤ, MvPolynomial.eval ... P = ...`.
    Read the complete declaration of exists_mvPolynomial_eulerChar_tensorPowers:
    proper X, coherent F, invertible finite tuple, rational P, degree bound, and precisely
    these lattice evaluations. Verdict: the predicate selects the same polynomial.
    Coherence of i_*O_Z follows since X is Noetherian and i is closed, and the support
    is i(Z). Snapper gives existence. Uniqueness holds because a rational polynomial
    vanishing at every integer tuple is zero (induction on the number of variables,
    using infinitely many roots in the last variable). Epsilon therefore does not
    introduce arbitrary mathematical data on valid inputs. No witness or coherence
    assumption was added to the signature. The degree bound is a consequence expressly
    outside the node's definition, so omitting it from the selection predicate is correct.
12. Required coefficient: `.coeff (Finsupp.onFinset Finset.univ
    (fun _ : Fin d => 1) (fun _ _ => Finset.mem_univ _))`.
    Verdict: exactly the coefficient of the product of all variables, with no factorial
    normalization. ℚ is correct: integrality is a later theorem, not this definition.
13. All bundles equal: selfIntersectionNumber calls intersectionNumber with
    `(fun _ : Fin d => L)` and `[L.IsInvertible]`. Verdict: exact repeated-module convention.

Edge cases: Fin 0 is empty, the factor list is empty, and the Finsupp exponent vector
is zero, so d=0 extracts the constant χ(X,i_*O_Z); epsilon still has a unique polynomial
because every zero-variable polynomial is constant. No nonempty index hypothesis was
added. Zero exponents use tensor units, negative exponents use the actual dual.
The zero polynomial is allowed by the predicate. Nonempty Z rules out the zero structure
sheaf and forces nonempty X via i; empty Z and empty X are excluded exactly as in the
node. Infinite dimension is incompatible with the stated finite d, as intended.
Characteristic zero and positive characteristic are both permitted. `universe u` is
explicit and arbitrary; the common universe is inherited from the scheme morphisms
and recorded Snapper statement. Schemes and fields from smaller universes can be lifted
to a common one, so this excludes no mathematical case. No independent test-object
universe or unbound variable occurs.

Independent H4 searches, with different conceptual terms:

- msearch.py leanfinder: "mixed intersection multiplicity invertible sheaves Euler
  polynomial coefficient"; eight hits on affine-open powers, fractional-ideal counts,
  and Proj.pow_apply, none defining this notion.
- msearch.py loogle: "MvPolynomial.coeff"; unknown identifier in that service, zero hits.
  The worker already opened its local Mathlib declaration; the actual module compiles
  against the local coefficient API.
- msearch.py leansearch: "intersection multiplicity of invertible sheaves on a proper
  scheme defined by an Euler characteristic polynomial"; Internal Server Error,
  recorded as unavailable, not a successful negative search.
- msearch.py grep: "intersection multiplicity|numerical intersection|intersectionNumber";
  zero hits.
- Independent rg over upstream WeilConjectures, Mathlib/AlgebraicGeometry, and base
  lean/Sheaf: "intersectionnumber|intersection_number|intersection number|numerical
  intersection|mixed.*degree". Only an unrelated purity docstring matched mixed/degree;
  no defining declaration. rg in dag/lean_names_upstream.json for intersectionNumber and
  selfIntersectionNumber found nothing. The base project has Snapper's polynomial
  existence theorem but no intersection-number definition. No module should be dropped.

H5/H6/H8/H9: no sorry and no theorem occurs in the delivered module, no proof is hidden
inside a definition, and all data are expressed by existing constructions. Module and
both declaration docstrings name Tag 0BEP and the correct blueprint id. A definition
node has no proof steps to reproduce. Namespace, imports, explicit binders, and line
width are correct. The import of SnapperNumericalPolynomial supplies the tensor, dual,
Euler-characteristic and polynomial APIs; ClosedImmersion supplies the required class.
There are no new nodes, dependency modules, or statement correction in this delivery.

Mismatches found: none. Changed only this report; retained the Lean module and the
node's statement and lean record. The recorded lean.statement matches the declaration
signature verbatim under the project's whitespace normalization.

Validation: scompile.py F1 def-sc-intersection-number
lean/Sheaf/AlgebraicGeometry/IntersectionNumber.lean passed cleanly in 1.8 seconds
(exit 0), with no errors or warnings.
