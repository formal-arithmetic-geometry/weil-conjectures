## Worker report

The item is stated in `Sheaf.RingTheory.MinimalPresentationTor` as
`MvPolynomial.exists_minimalPresentationTor_equiv`. Its only proof is `sorry`.
The accompanying definition module `Sheaf.RingTheory.MinimalGradedPresentation`
bundles exactly the presentation data quantified over by the item, using existing
Mathlib notions. There are no hollow definitions and no auxiliary proofs.

Clause-by-clause correspondence:

- A field k: `(k : Type v) [Field k]`.
- S = k[x_0,x_1]: `MvPolynomial (Fin 2) k`.
- Total-degree grading: `MvPolynomial.IsHomogeneous` in the two scalar-compatibility
  fields `n_smul`, `f_smul` of `MinimalGradedPresentation`.
- S_+ = (x_0,x_1): `Ideal.span (Set.range (X : Fin 2 → S))`, abbreviated `I`.
- N is a finitely generated graded S-module: `P.N`, `P.finite`, `P.nGrading`,
  `P.nDecomposition`, and `P.n_smul`. Integer-indexed additive homogeneous components
  form an internal direct sum. Stability under k follows by applying `n_smul` to
  homogeneous constants of degree zero, so this is exactly an S-module grading.
- F is finite graded free: `P.F`, `P.fGrading`, `P.fDecomposition`, `P.f_smul`,
  and `P.basis : Module.Basis (Fin P.rank) S P.F` with `P.degree : Fin P.rank → ℤ`
  and `P.basis_mem`. Negative and positive shifts are both allowed.
- q is a graded presentation: `P.q`, `P.surjective`, and `P.graded`.
- The induced map F/S_+F → N/S_+N is an isomorphism: `P.minimal` says
  `q x ∈ I • ⊤ → x ∈ I • ⊤`. Linearity supplies the reverse containment;
  thus this is injectivity of the induced map. `P.surjective` supplies its
  surjectivity. Hence this formulation is equivalent, with no additional hypothesis.
- K = ker(q): `LinearMap.ker P.q`, with its own inherited S-module structure.
- K/S_+K: `LinearMap.ker P.q ⧸ (I • (⊤ : Submodule S (LinearMap.ker P.q)))`.
  Importantly, this is ideal multiplication inside K, not the ambient submodule IF.
- Tor_1^S(N,k): `((Tor' (ModuleCat S) 1).obj P.N).obj residue`.
  Here `residue` is k restricted along `MvPolynomial.constantCoeff : S →+* k`;
  each X acts as zero, so this is precisely the residue S-module in the node.
- Natural isomorphism: the existential family `e P` of S-linear equivalences is
  oriented from K/IK to Tor_1. Its inverse is the orientation displayed in the node.
  The last conjunct asserts naturality for every commuting square of degree-zero
  maps `a`, `b`. The map `c` is the induced kernel map, specified by
  `(c x : Q.F) = a (x : P.F)`. It exists uniquely for every commuting square.
  Equality is imposed on every quotient generator `mkQ x`, which suffices for the
  full commuting square because `mkQ` is surjective. The Tor map is the recorded
  bifunctor's `T.map (ModuleCat.ofHom b)` evaluated at the fixed residue module.
- Consequence Tor_1 = 0 implies K/IK = 0: the first conjunct uses `Subsingleton`
  for both modules, which means exactly that every element equals zero.

Dependency declarations read and used:

- `def-weil-pbc-tor-modules` has status mathlib; its `mathlib_match` names
  `CategoryTheory.Tor'` in `Mathlib.CategoryTheory.Monoidal.Tor` (signature and
  docstring read). This is first-variable Tor, as required. The module-category
  instances are supplied by the imports `ModuleCat.Abelian`, `ModuleCat.Projective`
  and `ModuleCat.Monoidal.Basic`.
- `def-sc-p1-standard` records `AlgebraicGeometry.ProjectiveLine.TwistData` in
  `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits`. Its complete
  signature and docstring were read. That is geometric twist data, not a polynomial
  grading or a module presentation, and the current statement contains no twist
  sheaf or geometric cover. Its reference provides context only. We retain this
  dependency but do not import its unused geometric module or duplicate TwistData.
  The polynomial ring and its grading are given directly by Mathlib's
  `MvPolynomial` and `MvPolynomial.IsHomogeneous`.
- The added dependency `def-sc-p1-minimal-graded-presentation` supplies
  `MvPolynomial.MinimalGradedPresentation`; its module is imported by the item.
- Mathlib definitions used directly include `DirectSum.IsInternal` (full definition
  read in Algebra/DirectSum/Basic), `Module.Basis` (Basis/Defs), `Module.Finite`
  (Finiteness/Defs), `ModuleCat.restrictScalars` (ChangeOfRings),
  `MvPolynomial.constantCoeff`, ideal/submodule products, and `Submodule.mkQ`.

Source and edge cases: read the blueprint source file on the server (it is not
present in this machine's literature checkout). It gives finite graded free
resolutions with arbitrary integer shifts; this item is the stage-1 minimal-kernel
refinement of that argument. The blueprint itself does not contain a graded
Nakayama or K₂ passage; see the source-locator correction in the second reading. For N=0, minimality forces F/IF=0, hence F=0 for finite
free F; the statement reduces to 0≅0. For N=S with identity presentation, K=0 and
Tor_1=0. For N=k with F=S and q=constantCoeff, K=I, K/IK=I/I² has dimension two;
Tor_1(k,k) also has dimension two. Rank zero and the empty basis are allowed.
All characteristics, finite fields, negative shifts and modules with multiple
homogeneous degrees are covered. The universe parameter is explicit; placing
k and modules in one common universe matches Mathlib's monoidal ModuleCat and
can be enlarged to encompass any given field and modules.
No statement correction or disputed mathematical assertion is needed.

Searches (executed through msearch.py; logged in searches.jsonl):

- LeanFinder: `Tor one of module naturally isomorphic kernel of minimal graded free
  presentation modulo irrelevant ideal`: eight hits (irrelevant ideal, Kähler
  differentials, representation Tor), none is this statement.
- Loogle initial query `CategoryTheory.Tor\u0027, LinearMap.ker` was rejected due to
  the literal escape; the successful follow-up `MvPolynomial.IsHomogeneous` gives
  the homogeneous polynomial predicate and eleven associated lemmas, not a minimal
  presentation or this Tor theorem.
- LeanSearch: `minimal graded free presentation Tor kernel quotient` and
  `minimal graded free presentation homogeneous basis`: service returned Internal
  Server Error. Unavailability is recorded, with no claim of a negative result.
- Mathlib grep: `minimal.*presentation|Tor.*ker|GradedModule` in RingTheory produced
  irrelevant kernel/quotient hits. Focused grep
  `MinimalGradedPresentation|minimal.*graded.*presentation|graded.*free.*presentation`
  returned zero hits. Additional rg in CategoryTheory/LinearAlgebra found no theorem.
- Source and landed Sheaf searches by the same presentation patterns, and source
  grep by the exact item id, found no declarations. Upstream names also have no
  `MinimalGradedPresentation` or `minimalPresentationTor` collision.
- DAG search by minimal graded presentation patterns found only this statement and
  `lem-sc-p1-graded-nakayama-free`, not a definition node. `blueprint_refs.py search
  'minimal graded'` found zero blueprint nodes.

Server compilation of the two modules together passed without errors or warnings.
The initial combined-file compile rejected a repeated universe name; the modules
now use distinct explicitly declared universe names and the second compile passed.

## New nodes

`def-sc-p1-minimal-graded-presentation` defines the minimal finite graded free
presentation data needed to quantify the natural family in this item. Its source
is the same blueprint resolution argument and the minimal presentation in this
stage-1 refinement. The definition spells out the ring, internal Z-gradings,
scalar compatibility, finite generation, finite homogeneous basis, degree-zero
surjection and equivalent injectivity condition modulo (x_0,x_1). It uses Mathlib
components rather than defining any of them again. No existing DAG definition,
Mathlib bundle, upstream declaration or landed Sheaf declaration was found.
Additional definition-specific LeanFinder search `finite graded free module
homogeneous basis minimal surjective presentation induces isomorphism modulo
irrelevant ideal` returned graded algebra generators/localization lemmas, none
bundling this notion. Loogle, grep and unavailable LeanSearch are recorded above
and in the new node. There are no dependency replacement modules.


## Second reading by M1

Independent reading of the sandbox node, both complete modules, the dependency
nodes and their recorded declarations, and the blueprint and Stacks source text.
Verdict: the Lean states exactly the item, with an explicit natural family;
no mathematical signature or item statement needed repair.

Object/hypothesis/conclusion checklist (H3):

- Field k: `k : Type v`, `[Field k]`; correct, no characteristic restriction.
- S = k[x_0,x_1]: `S := MvPolynomial (Fin 2) k`; correct.
- Total-degree ring grading: `IsHomogeneous i` in the bundle's `n_smul`
  and `f_smul`; its Mathlib definition is weight-one homogeneity. Correct.
- S_+ = (x_0,x_1): `I := Ideal.span (Set.range X)`; correct.
- Finitely generated graded N: `P.N`, `P.finite`, `nGrading`,
  `nDecomposition`, `n_smul`; correct. `DirectSum.IsInternal` is bijectivity
  of the canonical additive direct-sum map, not only spanning. Stacks 00JL
  defines graded modules using precisely integer-indexed additive components
  and degree-additive scalar multiplication, including negative module degrees.
- Finite graded free F: `P.F`, `fGrading`, `fDecomposition`, `f_smul`,
  `rank`, `basis : Module.Basis (Fin rank) S F`, `degree`, `basis_mem`;
  correct. A chosen homogeneous finite basis is presentation data, and every
  finite graded free module admits such data; it adds no property hypothesis.
- Graded surjection q: `P.q`, `P.surjective`, `P.graded`; correct.
- Induced F/IF -> N/IN isomorphism: `P.minimal` says q^{-1}(IN) subset IF.
  S-linearity implies IF subset q^{-1}(IN); surjectivity of q implies
  surjectivity on quotients. Thus this is exactly the required quotient
  isomorphism, with neither extra nor missing conditions.
- Kernel K: `LinearMap.ker P.q`, with its inherited S-module; correct.
- K/IK: the quotient by `I • (⊤ : Submodule S (LinearMap.ker P.q))`;
  correct. Multiplication takes place in K, so this is not K/(K intersect IF).
- Residue k: restriction of the regular k-module along `constantCoeff`;
  correct S-action, with both variables acting by zero and constants by
  their values. This identifies k with S/I.
- Tor_1(N,k): `(T.obj P.N).obj residue`, `T := Tor' (ModuleCat S) 1`;
  correct. Read `CategoryTheory.Tor'`: it derives the first variable of
  tensor, exactly the dependency `def-weil-pbc-tor-modules`.
- Natural isomorphism: `∃ e : ∀ P, K/IK ≃ₗ[S] Tor_1(N,k)`;
  correct orientation after inversion. The final conjunct quantifies over
  every graded commuting square `(a,b)` and the kernel map `c`. Commutativity
  ensures the restriction c exists, and the stated equation on its values
  specifies it uniquely. Naturality on all `mkQ x` is equivalent to the
  quotient-map square because mkQ is surjective. The equivalence family is
  chosen before the morphisms, so the naturality quantifiers are correct.
- Consequence Tor_1 = 0 implies K/IK = 0: the first conjunct's implication
  between `Subsingleton` instances; correct for additive modules.

Dependencies / new node (H4, H12, H13): opened the complete signature of
`AlgebraicGeometry.ProjectiveLine.TwistData` in TransitionUnits. It concerns
geometric twists and trivializing sections, not the algebraic presentation
used here. The item's reference to `def-sc-p1-standard` is contextual; no
geometric datum is required or copied. The Tor node's recorded Mathlib
specialization supplies the actual Tor used. The new definition node
`def-sc-p1-minimal-graded-presentation` was read field by field against its
structure: its statement describes all and only the bundle fields, and it
uses existing Mathlib component notions rather than duplicating them.
Its empty stmt_deps is appropriate: none of the existing DAG nodes defines
this algebraic bundle, and its components are foundational Mathlib notions.
Its source is the blueprint's finite sums of S(d), together with the
stage-1 item's minimality condition. The source locator was repaired to say
this precisely. The remaining new-node fields satisfy brief-stage2 section 5:
new definition id, chapter/unit, created item/group, empty proofs, null match,
three search kinds, ancestor/via, none audits, and complete Lean record.
There are no dependency replacement modules.

Edge cases: rank zero (`Fin 0`) and the zero target are allowed and give
K = 0; N = S with q = identity gives K = Tor_1 = 0; N = k with q =
constantCoeff gives K = I and K/IK = I/I², dimension two, agreeing with
Tor_1(k,k). No lower-degree bound, positive rank, nonzero module, field-size
or characteristic assumption is inserted. Negative shifts are represented
by integer basis degrees. The degree-zero compatibility condition includes
constants, so it also enforces k-stability of components. Empty schemes
and geometric covers are not quantified over in this algebraic item.
Universes are explicitly bound: a common arbitrary universe for the field
and modules is the ModuleCat monoidal convention; cumulativity allows any
field and any given pair of module sizes in a sufficiently large common
universe. There is no fixed small-universe bound or unbound implicit variable.

Independent searches (queries recorded in searches.jsonl): LeanFinder
`First Tor module of a residue field is the relations modulo the maximal ideal
for a minimal free cover` returned cotangent/Kaehler and residue tensor
results, no exact theorem or bundle. Loogle `CategoryTheory.Tor'` returned
Tor', its projective vanishing theorem and generated functor formulas,
none the item. An initial literal escape query was rejected and supplies
no evidence. LeanSearch `minimal free cover kernel tensor residue field
first Tor` returned Internal Server Error; no negative conclusion is drawn
from that service. Grep of Mathlib for minimal graded/presentation, graded
free presentation, and Tor/kernel patterns returned only unrelated results.
Independent rg of WeilConjectures and landed lean/Sheaf for minimal
presentation/graded free presentation found no existing bundle or theorem;
DAG search finds the item and graded Nakayama argument, not a definition.
The upstream declaration-name registry has no delivered-name collision.

Mismatches repaired: the theorem's two source docstrings claimed the
blueprint proof contained a graded Nakayama criterion applied to K₂. Direct
reading on the server shows it only quotes graded Hilbert syzygy and then
sheafifies; this Tor calculation is a stage-1 refinement. Reworded both
source docstrings, corrected the new definition node's source.place, and
clarified the worker report. Also replaced the ambiguous docstring phrase
"second clause" by "zero-module consequence". The inherited item source
locator is recorded as inaccurate here, but its fixed source field and
mathematical statement remain unchanged. No statement_change is needed:
the statement is valid and the blueprint unit statement is unaffected.

The proof docstring follows all three DAG proof steps and names their
supporting nodes. Both modules have source/blueprint docstrings, no hollow
data, no auxiliary proved theorem, and only the item's named `sorry`.
The Lean records' signatures remain verbatim equal to the unchanged files.

Validation after repairs: scompile.py compiled both modules together in
2.3 seconds, exit 0, with no errors or warnings. deliver2.py --no-push
printed OK: the packet passes preflight and compiles.
