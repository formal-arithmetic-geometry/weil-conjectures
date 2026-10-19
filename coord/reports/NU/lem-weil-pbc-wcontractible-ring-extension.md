## Worker report

The module `Sheaf.RingTheory.BoundedWContractibleExtension` states
`RingHom.exists_bounded_wContractible_extension`, with its sole proof `by sorry`.
No definitions, new nodes, dependency repairs, or statement corrections are needed.

Clause-by-clause match:

- A commutative ring A: `(A : Type u) [CommRing A]`.
- An infinite cardinal κ: `(κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ)`.
- The size assumption: `(hA : Cardinal.mk A ≤ κ)`.
- A commutative ring D and a map A → D: `∃ (D : Type u) (_ : CommRing D)
  (f : A →+* D)`.
- Faithful flatness and ind-etaleness: `f.FaithfullyFlat ∧ f.IndEtale`.
- The bound |D| ≤ κ^(2^(2^(2^κ))): `Cardinal.mk D ≤ κ ^
  ((2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ κ)))`.
  Each exponent is a cardinal exponent, not natural-number exponentiation.
- Every faithfully flat weakly etale map D → B: `∀ (B : Type (max u v))
  [CommRing B] (g : D →+* B), g.FaithfullyFlat → g.WeaklyEtale → ...`.
- Its ring retraction and composite identity: `∃ r : B →+* D,
  r.comp g = RingHom.id D`.
- The induced affine spectrum map is a one-member pro-etale covering:
  `Presieve.singleton (Spec.map (CommRingCat.ofHom f)) ∈
  Scheme.proetalePrecoverage (Spec (CommRingCat.of A))`.

Dependency declarations read and used:

- `def-weil-pbc-faithfully-flat-ring-map`: `RingHom.FaithfullyFlat`, in
  `Mathlib.RingTheory.RingHom.FaithfullyFlat`. Its definition uses the map's algebra
  structure and `Module.FaithfullyFlat`, from the node's recorded module
  `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic` (publicly imported transitively).
- `def-weil-pbc-ind-etale-algebra`: recorded module
  `Sheaf.RingTheory.IndPrincipalZariski` publicly imports the upstream
  `WeilConjectures.RingTheory.ProEtale.IndEtale` declaration `RingHom.IndEtale`.
  This uses `Algebra.IndEtale`, whose stages are etale algebras in a filtered
  colimit presentation. For weak etaleness use `RingHom.WeaklyEtale`, from
  `WeilConjectures.RingTheory.ProEtale.WeaklyEtale`, defined by
  `Algebra.WeaklyEtale` on the algebra structure of the given map.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and
  `AlgebraicGeometry.Spec.map`, from `Mathlib.AlgebraicGeometry.Scheme`, exposed
  through the site import.
- `def-weil-pbc-proetale-covering`: its `mathlib_match`
  `AlgebraicGeometry.Scheme.proetalePrecoverage`, in
  `Mathlib.AlgebraicGeometry.Sites.Proetale`. This is `propQCPrecoverage
  @WeaklyEtale`: jointly surjective quasi-compact covering families of weakly
  etale morphisms. `Presieve.singleton` specifies exactly one member. The
  quasi-compact-cover condition is the finite affine-open condition in the node.

The module also imports the stated proof dependency
`Sheaf.RingTheory.IndEtaleStability`, and the Mathlib proof dependencies in
`Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra`,
`Mathlib.AlgebraicGeometry.Pullbacks`, and
`Mathlib.AlgebraicGeometry.Morphisms.Affine`. Unstated proof dependencies are
not needed to type this theorem and have no modules to import. Its docstring
carries all six proof steps from the DAG, including the cardinal estimate and
verification of the covering on every affine open.

Source read: local `literature/stacks-project/proetale.tex`, proposition
`proposition-find-w-contractible` (0983) and following remark
`remark-size-w-contractible` (0984). Their construction and displayed cardinal
bound agree with the node. The splitting and covering interfaces are those
specified by the dependency nodes (0981, 0989).

Edge cases checked: no Nontrivial hypothesis excludes the zero ring; its empty
spectrum is allowed in the site. A singleton cover of the empty target is
legitimate. The empty product in the cardinal proof has size one and κ is
infinite. Finite rings and κ = aleph0 are allowed. The test ring universe is
`max u v`, at least the witness universe, so the retraction clause cannot be
vacuous because the test rings were placed in a smaller universe. The arbitrary
universe v allows larger extensions. A, D and κ share u, consistent with the
ind-etale filtered presentation API; the bound remains a small cardinal in u.

Searches for existing statements (2026-10-15):

- `msearch.py ... leanfinder "Every commutative ring has a faithfully flat ind
  etale extension to a w contractible ring with a cardinal bound"`: eight hits
  on finite-type descent and etale presentations, none stating this result.
- `msearch.py ... loogle "RingHom.IndEtale, RingHom.FaithfullyFlat"`: zero hits,
  unknown identifier RingHom.IndEtale in the Mathlib-only index.
- `msearch.py ... grep "WContractible|wContractible|w.contractible|IndEtale"`:
  zero Mathlib hits.
- `msearch.py ... leansearch "Every ring admits a bounded faithfully flat ind
  etale extension splitting all faithfully flat weakly etale extensions"`:
  unavailable (Internal Server Error); no mathematical verdict inferred.
- `rg` in upstream WeilConjectures and project lean/Sheaf for
  `WContractible|wContractible|w.contractible|lem-weil-pbc-wcontractible-ring-extension|exists.*indEtale`:
  upstream WContractible and WeaklyEtaleIndEtale files found; no same bounded
  statement in the project. Read `exists_isWContractibleRing` and
  `IsWContractibleRing.exists_retraction`: the former has no cardinal bound,
  and the latter directly splits only ind-etale extensions. Neither says
  the whole node's statement, so an existing:true attachment would be wrong.
- `rg` in dag/lean_names_upstream.json for
  `exists_bounded_wContractible_extension|exists_isWContractibleRing`: no hits.
  The new full declaration name is absent from Mathlib, upstream and lean/Sheaf.

Validation: `scompile.py NU lem-weil-pbc-wcontractible-ring-extension` on the
module passed, with no errors or warnings (1.4 seconds for the module, nice 19,
two threads, per-file limit 60 seconds). No local compiler was run.

No node faults or STATEMENT-DISPUTED issues found.


## Second reading by NU

Independent reading of the sandbox node and module, Stacks proetale.tex
`definition-w-contractible` (0981), `proposition-find-w-contractible` (0983),
`remark-size-w-contractible` (0984), and `definition-fpqc-covering` (0989).
The section assumes only a commutative ring; no nonzero, characteristic,
Noetherian, or finiteness hypothesis is implicit.

Object/hypothesis/conclusion inventory, with the corresponding Lean and verdict:

1. Arbitrary commutative A: `(A : Type u) [CommRing A]`. Exact.
2. Infinite cardinal kappa: `(κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ)`.
   Exact; infinity is a hypothesis, not regularity or an uncountability requirement.
3. Size of A at most kappa: `(hA : Cardinal.mk A ≤ κ)`. Exact.
4. A single commutative witness D and ring map from A:
   `∃ (D : Type u) (_ : CommRing D) (f : A →+* D)`. Exact. All subsequent
   clauses refer to this same witness and this same map.
5. Faithfully flat and ind-etale: `f.FaithfullyFlat ∧ f.IndEtale`. Exact.
   Opened the dependency records and IndPrincipalZariski public imports,
   Algebra.IndEtale and RingHom.IndEtale in upstream IndEtale.lean, and
   Mathlib RingHom.FaithfullyFlat. These use f.toAlgebra, with no unrelated
   algebra instance. Etale stages include finite presentation. The unused
   principal ind-Zariski clause is not substituted for ind-etaleness.
6. Bound on D: `Cardinal.mk D ≤ κ ^ ((2 : Cardinal.{u}) ^
   ((2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ κ)))`. Exact: three powers
   of two, all cardinal powers, then kappa to that exponent, as in 0984.
7. Every commutative test ring B and faithfully flat weakly etale g from D:
   `∀ (B : Type (max u v)) [CommRing B] (g : D →+* B),
   g.FaithfullyFlat → g.WeaklyEtale → ...`. Exact. Opened upstream
   RingHom.WeaklyEtale and Mathlib Algebra.WeaklyEtale: flatness of the
   algebra and flatness of its tensor multiplication are the node's notion.
   No ind-etaleness assumption is imposed on g.
8. A ring retraction for each such g: `∃ r : B →+* D,
   r.comp g = RingHom.id D`. Exact; composition has the correct direction.
   D precedes B and g; r depends on g, as required.
9. The induced map Spec D to Spec A is a one-member pro-etale covering:
   `Presieve.singleton (Spec.map (CommRingCat.ofHom f)) ∈
   Scheme.proetalePrecoverage (Spec (CommRingCat.of A))`. Exact. Opened
   Mathlib Spec and Spec.map, proetalePrecoverage, propQCPrecoverage,
   qcPrecoverage and QuasiCompactCover. This is covering-family membership,
   with weak etaleness, joint surjectivity and the compact-open condition;
   the finite-affine-open formulation is supplied by
   QuasiCompactCover.exists_isAffineOpen_of_isCompact. No replacement by
   mere membership in the generated topology occurs.

Edge cases: zero A and D are allowed (no Nontrivial binder); their empty
spectra are allowed, including a singleton covering of the empty target.
Finite rings and kappa = aleph0 are included. The source's n=0 affine-open
covering case is allowed by the precoverage. No integer degree or characteristic
restriction occurs. The bound lies in universe u; set-sized constructions
preserve that universe, so D : Type u is legitimate. Test rings have universe
max u v, never smaller than D; arbitrary v permits larger test rings, and v=0
includes same-universe extensions. There are no implicit unbound variables.

Independent searches: msearch leanfinder queried "A commutative ring admits a
size bounded universally split weakly etale faithfully flat algebra": eight
hits about etale algebras, smoothness and finite-type descent, none this result.
msearch loogle queried `"Etale", "FaithfullyFlat"`: two descent hits, neither
this result. msearch grep queried
`contractification|contractible.*ring|bounded.*[Ee]tale`: one unrelated
locally-contractible-space documentation hit, no matching ring statement.
Direct rg searched Mathlib, upstream WeilConjectures, project lean/Sheaf and
lean_names_upstream.json for WContractible, wContractible, w.contractible and
the new theorem name. Opened upstream exists_isWContractibleRing and
IsWContractibleRing.exists_retraction: the first omits the cardinal bound;
the second only splits ind-etale maps. Neither is an exact existing statement.
No new definition node or dependency module is needed. The recorded dependency
modules give the notions used; the full IndEtaleStability signature was also
read as the available proof dependency.

No mathematical mismatch found and no Lean or node changes made. The sole
postponed theorem has a source/blueprint docstring carrying all six node proof
steps, including the cardinal injection and the affine-open covering argument.
There is no hollow definition or proved helper. Checked the node's lean.statement
verbatim against the signature and all Lean lines against the 100-character limit.
No statement correction or citer audit is required.

Validation: server scompile.py compiled BoundedWContractibleExtension.lean cleanly
in 1.4 seconds, with its side imports IndPrincipalZariski and IndEtaleStability
also clean (1.3 and 1.4 seconds). Nice 19, two threads, 60 seconds per file;
no local compiler or library build. The initial relative-path invocation could
not find the sandbox file; rerunning with its absolute path succeeded.
