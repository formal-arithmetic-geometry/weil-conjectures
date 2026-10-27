## Worker report

This delivery states `AlgebraicGeometry.exists_equivariant_finite_residue_domination`
in `Sheaf.AlgebraicGeometry.EquivariantFiniteResidueDomination`. Its only theorem
has proof `by sorry`. There are no new definitions, dependency repairs, new DAG
nodes, or statement corrections. The original node changes only in `lean`.

Source checked: de Jong, *Families of curves and alterations* (1997),
Situation 5.3, printed p.613, and Lemma 5.6, printed p.614, in the publisher PDF:
https://aif.centre-mersenne.org/item/10.5802/aif.1575.pdf . The latter gives a finite
generically etale equivariant alteration containing prescribed finite separable
residue extensions at every point over the prescribed points. Apply it to finite
Galois splitting fields of the finite etale residue algebras and normalize the
cover, as in the DAG proof. This gives the node's finite-etale-scheme formulation.
The full fourteen-step DAG proof, including the empty case, coefficient lifting,
Galois receiving field, paired group extension, normalization, generic etaleness,
and the all-points residue splitting argument, is in the theorem docstring.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The field is `(k : Type u) [Field k]`.
- The specified k-scheme is `(S : Scheme.{u}) (pS : S ⟶ Spec (.of k))`.
- Integrality is `[IsIntegral S]`; normality is `hnormal`, requiring both
  `IsDomain (S.presheaf.stalk s)` and `IsIntegrallyClosed` at every point.
- Projectivity is `[IsHProjective pS]`, the node's finite projective-space
  embedding convention. Finite type is the two classes
  `[LocallyOfFiniteType pS] [QuasiCompact pS]` from its dependency record.
- The finite group is `(H : Type v) [Group H] [Finite H]`. No faithfulness,
  characteristic restriction, or geometric integrality is required.
- Its field and scheme actions are the actual monoid homomorphisms
  `σk : H →* (k ≃+* k)` and `σS : H →* Aut S`. The equation `hsemilinear`
  expresses compatibility with `pS`; the inverse in `σk h⁻¹` accounts for
  contravariance of Spec, as in the existing semilinear alteration modules.
- The finite list is `(r : ℕ) (s : Fin r → S)`; its points can be arbitrary,
  repeated, generic, closed, or nonclosed. No distinctness is assumed.
- The prescribed schemes are `(E : Fin r → Scheme.{u})` with structure maps
  `e i : E i ⟶ Spec (S.residueField (s i))`. The indexed instances `hefinite`
  and `heetale` say exactly that every structure map is finite and etale.
  They do not require a choice of component or any H-action on E.
- The output is an existential finite group J, with Group/Finite structures,
  a group homomorphism `ρ : J →* H`, and `Function.Surjective ρ`.
- `J : Type (max u v)` accommodates both the input group's universe and the
  finite Galois automorphism group in the scheme's universe. This imposes
  no restriction on input H and does not resize the input scheme.
- The output W has `[IsIntegral W]`, structure morphism pW, and the same
  projectivity, locally finite type, quasi-compactness, and stalk normality
  clauses as S, written as existential/conjunction data in the conclusion.
- `a : W ⟶ S` is over k by `a ≫ pS = pW`. Its asserted properties are
  `IsFinite a` and `Surjective a`.
- Generically etale is literally `∃ U : S.Opens, Dense (U : Set S) ∧
  Etale (a ∣_ U)`, not only a field-theoretic separability assertion.
- `σW : J →* Aut W` is the compatible output action. Its scalar action is
  precisely `σk` composed with ρ, by the equation involving `σk (ρ j⁻¹)`.
  The equation `(σW j).hom ≫ a = a ≫ (σS (ρ j)).hom` is equivariance.
- The function-field equality is expressed as equality of subsets inside
  W.functionField. The witness `ha : a (genericPoint W) = genericPoint S`
  fixes the canonical function-field inclusion to the generic stalk map
  `S.presheaf.stalkSpecializes (specializes_of_eq ha) ≫
  a.stalkMap (genericPoint W)`. Thus, for every z, membership in the image
  of k(S) is equivalent to being fixed by every `j : ρ.ker` under
  `Scheme.functionFieldAut (σW j.val)`. No arbitrary field embedding or
  arbitrary algebra structure replaces the map induced by a.
- The generic stalk is Mathlib's function field; for an integral scheme it
  is a field, and its canonical residue map is an isomorphism onto the
  generic residue field mentioned in the statement. `functionFieldAut`
  is the existing pullback action. Using all elements of the kernel gives
  the same fixed subfield whether pullback or its inverse is used.
- The last clause quantifies over every `i`, every `w`, and every equality
  `hw : a w = s i`. The base-change field map is the actual
  `a.residueFieldMap w`, preceded by the equality transport
  `eqToHom (congrArg S.residueField hw.symm)`. This has source κ(s_i),
  target κ(w); Spec reverses it, giving exactly the map for the pullback.
- `ι` is an isomorphism from that pullback to the actual finite coproduct
  `∐ (fun _ : Fin n ↦ Spec (W.residueField w))`. The final equation
  with `Sigma.desc (fun _ ↦ 𝟙 _)` and `pullback.snd` says the isomorphism
  is over κ(w), rather than merely an isomorphism of underlying schemes.
  The number n is allowed to be zero.

Dependency declarations used:

- `Field` (`Mathlib.Algebra.Field.Defs`).
- `AlgebraicGeometry.IsIntegral` (`Mathlib.AlgebraicGeometry.Properties`).
- `AlgebraicGeometry.IsHProjective`
  (`WeilConjectures.AlgebraicGeometry.Morphisms.Projective`).
- `AlgebraicGeometry.LocallyOfFiniteType` and `QuasiCompact`
  (`Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `...QuasiCompact`).
- `AlgebraicGeometry.IsFinite` (`Mathlib.AlgebraicGeometry.Morphisms.Finite`).
- `AlgebraicGeometry.Surjective`
  (`Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`).
- `AlgebraicGeometry.Etale` (`Mathlib.AlgebraicGeometry.Morphisms.Etale`).
- `AlgebraicGeometry.Scheme.residueField` and `Scheme.Hom.residueFieldMap`
  (`Mathlib.AlgebraicGeometry.ResidueField`).
- The arbitrary integral-scheme clause of `def-sc-function-field` uses
  Mathlib's `Scheme.functionField`, publicly reexported by the recorded
  module `WeilConjectures.AlgebraicGeometry.FunctionField`; the separate
  component-product declaration is not needed for this integral scheme.
- `CategoryTheory.Limits.pullback`, `pullback.snd`
  (`Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`).
- Additional existing canonical constructions: `Scheme.functionFieldAut`
  (`WeilConjectures.AlgebraicGeometry.StalkAut`), coproducts and `Sigma.desc`
  (`Mathlib.AlgebraicGeometry.Limits`), and restricted scheme morphisms
  (`Mathlib.AlgebraicGeometry.Restrict`). Normality is the explicit stalk
  predicate in the node, using `IsDomain` and `IsIntegrallyClosed`.

Every recorded project module of a stated proof dependency is imported
nonpublicly, as are the relevant matched Mathlib modules. In particular the
normalization, finite-over-projective, flat-fibre etale, generic-fibre spreading,
finite-Galois receiving, and polynomial Chinese remainder interfaces are imported.
No duplicate notion, canonical map, or action construction is introduced.

Edge cases checked before writing and rechecked against the signature:

- `r = 0`: there is no hidden nonempty-index instance; take W=S, J=H, ρ=id,
  a=id mathematically. The invariant clause reduces to the whole field.
- Empty E_i: finite etale includes the empty scheme, and n=0 gives its
  empty coproduct after base change. No nonempty E_i condition appears.
- Trivial H and nonfaithful actions on k or S: no injectivity conditions;
  the paired group construction in the proof retains the prescribed H.
- Dimension-zero S, including Spec k, and prescribed generic points:
  neither a dimension condition nor a closed-point condition occurs.
- Positive characteristic and imperfect k: no characteristic-zero or
  perfectness assumption; only the input residue schemes are etale.
- Every point above s_i is covered, not a selected point or an existential
  residue embedding. The isomorphism must commute with its base projection.
- Empty S is already excluded by the node's integrality hypothesis; it is
  not separately assumed nonempty. Fin n indexes only finite coproducts,
  which exist in Scheme.{u}, including n=0, for any universe u.

Searches for an existing statement (all through prescribed tools/read-only sources):

- `msearch.py ... leanfinder "A finite equivariant generically etale cover of a
  normal integral projective scheme splitting finite etale residue schemes"`:
  8 results, including generic etale/normalization declarations; no such theorem.
- `msearch.py ... leansearch "finite equivariant covers splitting prescribed
  finite etale residue schemes"`: 8 generic etale site/cover results; no theorem.
- `msearch.py ... loogle "AlgebraicGeometry.Scheme.functionField,
  AlgebraicGeometry.Scheme.Hom.residueFieldMap"`: 0 hits.
- `msearch.py ... grep "functionFieldMap|genericallyEtale|GenericallyEtale"
  AlgebraicGeometry`: 0 Mathlib hits.
- Read-only rg over WeilConjectures and Sheaf for equivariant/residue domination,
  generic etaleness, and function-field actions: related finite quasi-splitting
  and semilinear Galois alteration theorems, but no finite prescribed-residue
  theorem. Found and reused `Scheme.functionFieldAut` in upstream StalkAut.
- Exact node-id search in WeilConjectures found no declaration. Searches for
  `residue_domination|residueDomination|exists_equivariant_finite_residue`
  in WeilConjectures, Sheaf, and `dag/lean_names_upstream.json` found no match.
- Read the node's ten statement dependency records and the complete signatures
  and docstrings of their corresponding declarations. The retired compact-object
  example was checked through its current upstream record and source module.

Validation: the initial module compiled cleanly with scompile.py on the server,
2.7 s for its sandbox compilation and 2.6 s for its library-name compilation.
The final file additionally imports the explicitly recorded Mathlib proof modules;
its compile and delivery preflight are recorded below after they run.
No STATEMENT-DISPUTED issue or node fault was found.

## Second reading by NN

Reread the node and the completed Lean signature after the initial server check.
This is a second pass by the same dispatched worker; no other agent was started.
The maintainer supplies the independent review after delivery.

The reread checked all four inputs (k/S, finite H and compatible actions, arbitrary
finite point list, finite etale E_i), and all outputs (finite J and surjective ρ,
normal integral projective finite-type W, a finite surjective over-k map, dense-open
etaleness, both action equations, the exact kernel fixed-field equality, and the
κ(w)-linear finite-coproduct splitting at every point above every s_i). In particular,
`hw.symm` transports κ(s_i) to κ(a w) in the correct direction before applying
`a.residueFieldMap w`; the generic-point specialization also points from the
canonical generic stalk to the stalk over its image. Both potentially erroneous
identifications were checked against the declared types and server compilation.
There are no hidden faithfulness, nonempty E_i, distinctness, closedness, smoothness,
or geometric integrality assumptions. No mathematical mismatch was found. Explicit
imports of the recorded integral/field/quasi-compact definitions and the Mathlib
proof modules were added on this pass; the signature was not changed.

Final validation: scompile.py compiled the complete final import set cleanly in
2.4 s (sandbox name) and 2.5 s (library name), with no errors or unexpected warnings.
`deliver2.py NN lem-sfb-equivariant-finite-residue-domination --no-push` printed
`OK (dry run): commit 26e3ff7ffa3 passes the preflight and compiles; nothing pushed`.
The dry-run staged exactly the module, its one node record, and this report.
A structural comparison confirmed that `lean` is the sole changed node field,
there is exactly one `sorry`, autoImplicit is disabled, and no Lean line exceeds
100 characters. This paragraph records those completed checks; the delivery tool
rechecks the resulting packet before pushing it.
