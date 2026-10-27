## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.BorelRootProductCoordinates` states
`AlgebraicGeometry.borel_root_product_coordinates`, with one `sorry` and no new
definitions. The original DAG statement and all dependencies are unchanged. Only
its `lean` record is added. There are no new nodes or dependency repairs.

Source read: Milne, Algebraic Groups (2017), printed p.445, Theorem 21.68(a) and
its proof, together with Remark 21.69 (p.446). This states multiplication is a
T-equivariant isomorphism for an arbitrary ordering. The existing parametrization
node identifies root subgroups by their smooth connected closed normalized
inclusions and their tangent images, so the theorem accepts any representatives
with precisely those properties. It does not select objects from a mere existence
statement. The entire five-step DAG proof is included in the theorem docstring.

Hypothesis and clause correspondence:

- The algebraically closed field is `{F : Type u} [Field F] [IsAlgClosed F]`.
  `u` is explicit, and `set_option autoImplicit false` checks all binders.
- Group schemes are `Grp (Over (Spec (.of F)))`, the recorded group-scheme
  interface. `hG : ReductiveTorusCentralizer.IsReductive G` supplies exactly the
  smooth connected affine finite-type reductivity convention from the dependency.
- `iT`, `hT`, and `hsplit` give the split maximal torus, using the recorded
  `IsMaximalTorus` and `MultiplicativeType.splitTorus`. `iB`, `hB`, `j`, and `hj`
  give the Borel inclusion and the compatible inclusion T into B.
- `aG`, `aB`, `haG`, and `haB` specify the actual conjugation actions used for
  character weights. They do not assume a separate action or a new property:
  both actions are pinned by composition with `GrpObj.conj`.
- `U`, `iU`, `hUclosed`, `hUnormal`, `hUsmooth`, `hUconn`, `hUunip`, `hUmax`
  express exactly the radical in the recorded Borel-pair statement: smooth
  connected normal closed unipotent subgroup, containing every such subgroup.
  There is no added splitting or coordinate hypothesis on U.
- `r`, `α`, `hαinj`, and `hαpos` enumerate without repetitions precisely the
  nontrivial G-character weights which also occur in Lie(B). This is exactly
  Phi-positive, using the two final equivalences of
  `reductive_borel_pair_structure`. No abstract root datum is needed merely to
  enumerate this set. `α` consists of actual group-scheme characters, and the
  test is `χ.hom.hom ≠ 1`, not a differential of a character.
- `R`, `iR`, `hR` give the chosen root subgroups: closed, smooth, connected,
  stable under the specified torus conjugation, and with differential range
  equal to the character weight space. These are precisely the identifying
  properties and uniqueness interface of the recorded parametrization theorem.
  Its Ga-isomorphism and conjugation formula are available consequences, not
  extra hypotheses or private definitions.
- The first conclusion `∃ k : ∀ i : Fin r, R i ⟶ U` with
  `k i ≫ iU ≫ iB = iR i` is the factorization of every inclusion through U.
- `Pi.π (fun l : Fin r ↦ (R l).X) i` are the categorical product projections
  in the category of F-schemes. Composing with `(k i).hom.hom` and taking
  `(List.ofFn ...).prod` defines the actual multiplication map, in the order
  0 through r-1. `IsIso` states it is an F-scheme isomorphism. This is not an
  unspecified isomorphism or a pointwise bijection.
- The existential `aU` and `aR` are internal `ModObj` actions, pinned by the
  two displayed morphism equalities to conjugation through the given subgroup
  embeddings. The final equality is the componentwise-conjugation equivariance
  formula for multiplication, on every F-test-scheme W. Testing every W is
  exactly equality of the corresponding morphisms by Yoneda. In particular it
  includes nonreduced test algebras and does not restrict to rational points.
- For r=0, the categorical product is the terminal F-scheme, isomorphic to
  Spec F. `List.ofFn` is empty, and `.prod` is the identity group element in
  Hom(product,U), hence the unit morphism. Its `IsIso` assertion states U=1.
  No extra nonempty-index hypothesis excludes this case.

Dependency declarations and modules read and used:

- `Field`: Mathlib.Algebra.Field.Defs (definition and field docstring read).
- `IsAlgClosed`: Mathlib.FieldTheory.IsAlgClosed.Basic (full signature and
  docstring read); the algebraic-closure node's match explicitly names this
  predicate when the field itself is algebraically closed.
- `CategoryTheory.Grp`, `GrpObj`, and group-object homomorphisms:
  Mathlib.CategoryTheory.Monoidal.Grp, with the specialized group-scheme
  documentation and subgroup definitions in
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs.
- `AlgebraicGeometry.reductive_borel_pair_structure`:
  Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure. Full
  signature and proof docstring read. The module publicly exposes the recorded
  reductivity, maximal-torus, Borel and character-tangent interfaces. Its
  positive-root characterization and radical characterization are used verbatim.
- `AlgebraicGeometry.TorusCharacterTangent.reductive_root_subgroup_parametrizations`:
  Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRootSubgroupParametrizations.
  Full signature and proof docstring read; its subgroup-identifying clauses
  give exactly `hR`. Its `IsStable` and `weightSpace` are reused from
  Sheaf.AlgebraicGeometry.TorusCharacterTangentWeights, without a second definition.
- `CategoryTheory.Limits.Pi.π` and finite products:
  Mathlib.CategoryTheory.Limits.Shapes.Products. `List.ofFn` supplies ordered
  finite enumeration; the existing group structure on Hom supplies `.prod`.

The proof-only nodes `lem-sfb-regular-cocharacter-borel-description`,
`lem-sfb-cocharacter-limit-smooth-structure`, and
`lem-sfb-positive-weight-equivariant-inverse` have no Lean records in the read
DAG. They require no statement objects for this theorem; their future imports
are omitted until they are stated. The other two proof dependencies are already
public statement dependencies. No import cycle is introduced.

Edge cases checked mathematically before writing and again against the signature:

- Empty root system / a torus / the trivial group: Fin 0, empty ordered product,
  unit morphism, trivial radical. No semisimplicity or positive-rank assumption.
- SL2: the single positive root subgroup maps isomorphically to U.
- GL3 and arbitrary ordering: in order 12,23,13 the coordinates are
  `(a,b,c) ↦ (a,b,c+ab)` on upper unitriangular matrices, with polynomial inverse
  `(a,b,d) ↦ (a,b,d-ab)`. Thus the order must not be replaced by a commutative
  Finset product. The implementation uses an ordered List product.
- Positive characteristic, including 2 and 3: no differential of a character,
  no denominators, no characteristic assumption. Tests quantify over all W.
- Representatives R and U are arbitrary actual group schemes with the recorded
  characterizations, not choices built on unproved existence.

Searches (2026-10-24):

- msearch.py leanfinder: "Ordered multiplication of positive root subgroup
  schemes in any order is a torus equivariant isomorphism onto the unipotent
  radical of a Borel subgroup". Eight hits: Geck cartanSubalgebra', EmbeddedG2
  indexEquivAllRoots and its apply/coe/symm lemmas, RootPairing.Equiv.weightEquiv_mul,
  Equiv.root_indexEquiv_eq_smul, baseOf_root_eq_baseOf_coroot, and Geck
  omegaConjLieSubmodule_eq_top_iff. These concern abstract root systems and
  Lie algebras, not products of subgroup schemes.
- msearch.py loogle: `"RootPairing", "Borel"`: zero hits.
- msearch.py grep: `root.?subgroup|unipotent.{0,20}radical|BorelSubgroup`:
  three hits in Mathlib/LinearAlgebra/Projectivization/PSL/Stabilizer.lean,
  concerning SL line stabilizers, not the general root-product theorem.
- msearch.py leansearch: "Multiplication of positive root subgroups is an
  isomorphism onto the unipotent radical of a Borel subgroup". Eight hits:
  Subgroup.mul, Positive.instMulSubtypeLtOfNat_mathlib,
  RootPairing.RootPositiveForm.toInvariantForm.congr_simp, RootPairing.posRootForm_eq,
  Units.posSubgroup.congr_simp, Prod.rootableBy, SemidirectProduct.mulEquivSubgroup,
  and RootPairing.RootPositiveForm.toInvariantForm. None is a scheme theorem.
- rg over lean/WeilConjectures and lean/Sheaf for root subgroup / unipotent
  radical and the proposed theorem name: no existing ordered-root-product
  theorem; existing Borel/root-parametrization modules were read and reused.
  `grep -rn 'lem-sfb-borel-root-product-coordinates' lean/WeilConjectures`
  found no declaration. The proposed name is absent from dag/lean_names_upstream.json,
  Mathlib, WeilConjectures, and Sheaf.

Validation: scompile.py compiled both sandbox and named library-module modes
cleanly (13.4 s / 4.8 s), with no unexpected warnings. The initial precedence
error in `Fin r → (T ⟶ ...)` was repaired before this clean compile. Every line
is at most 100 characters. No statement dispute or source correction is needed.

## Second reading by Q24

The dispatcher explicitly forbids starting other agents; this is a second pass
by the same worker, not an independent-agent review. The maintainer supplies the
independent review of the delivered statement.

I reopened the node and completed Lean file and checked every hypothesis and
clause against the correspondence above. In particular: no chosen root-system
base is required because the recorded Borel-pair theorem identifies Phi-positive
exactly with the nonzero Lie(B) character weights; `hαpos` uses that equivalence
rather than a new positivity predicate. `hR` uses the existing uniqueness
characterization of root subgroups. `hUmax` quantifies over every smooth connected
normal closed unipotent subgroup, exactly as the recorded radical does. The
multiplication is over the underlying F-scheme product and is an ordered List
product, so the noncommuting GL3 example is preserved. The equivariance actions
are conclusions pinned by inclusions, not arbitrary assumed actions; testing
all W implies the scheme-morphism identity. Fin 0 is admitted and gives the
unit isomorphism. No mathematical mismatch was found, and no statement or
additional dependency needed changing. The only implementation fix was the
parenthesized character-Hom type mentioned in validation.
