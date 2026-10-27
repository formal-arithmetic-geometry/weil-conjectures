## Worker report

The module `Sheaf.AlgebraicGeometry.ZeroVerschiebungPrimitiveGeneration` states
`AlgebraicGeometry.AffineGroupFrobeniusVerschiebung.zero_verschiebung_primitive_generation`.
Its sole proof is `sorry`. No definition, extra node, dependency repair, or statement
correction is needed. The node changes in `lean` and gains the landed definition node
`def-sfb-coordinate-hopf-algebra` in `stmt_deps`, as requested in the return.

The source was read directly in `literature/milne-algebraic-groups_iAG2017.pdf`,
Definition 14.45 and Proposition 14.48, printed pp. 295–296 (via pdftotext). Definition
14.45 identifies elementary unipotence with generation of the coordinate algebra by
homomorphisms to the additive group. On coordinates these are precisely the primitive
elements. Proposition 14.48 gives the zero-Verschiebung criterion without the additional
smoothness hypothesis used in the subsequent Proposition 14.49.

Hypothesis and clause correspondence:

- The field is `(k : Type u) [Field k]`; positive characteristic is
  `(p : ℕ) [Fact p.Prime] [CharP k p]`. A positive characteristic of a field is prime,
  so the prime binder expresses the stated characteristic, as in the dependency.
- The k-scheme is `(G : Scheme.{u}) [G.Over (Spec (CommRingCat.of k))]`.
  Its group law is `[GrpObj (G.asOver (Spec (CommRingCat.of k)))]`, and its
  commutativity is `[IsCommMonObj (G.asOver (Spec (CommRingCat.of k)))]`.
- Affineness is `[IsAffine G]`. Finite type is the two recorded components
  `[LocallyOfFiniteType (G ↘ Spec (CommRingCat.of k))]` and
  `[QuasiCompact (G ↘ Spec (CommRingCat.of k))]`.
- The coordinate algebra C is the actual global-section ring `Γ(G, ⊤)`. The canonical
  coordinate Hopf structure supplies `Coalgebra.comul (R := k)` and
  `Coalgebra.counit (R := k)`, not arbitrarily chosen operations.
- The twist is the dependency's `twist k p Γ(G, ⊤)`, the ring pushout along the field
  Frobenius. Its scalar structure is the dependency's `twistAlgebra`, from the second
  pushout factor; thus `algebraMap k (twist k p Γ(G, ⊤))` is precisely u^(p).
- In the dependency's `Maps`, the canonical Verschiebung comorphism is characterized
  on every coordinate by `projection k p Γ(G, ⊤) (iteratedComul k Γ(G, ⊤) p c)`.
  Hypothesis `hV` equates this expression with `algebraMap ... (Coalgebra.counit ... c)`
  for every c, exactly V* = u^(p) ε. It assumes neither an arbitrary candidate V nor
  just its action on geometric points. The dependency theorem establishes that this
  actual construction is the canonical group homomorphism.
- The conclusion quantifies `∀ c : Γ(G, ⊤)` and supplies a finite list
  `x : Fin n → Γ(G, ⊤)` and a polynomial `f : MvPolynomial (Fin n) k`.
- Each generator is primitive by the explicit equation
  `Coalgebra.comul (R := k) (x i) = x i ⊗ₜ[k] 1 + 1 ⊗ₜ[k] x i`.
  The expression `MvPolynomial.aeval x f = c` says that f, with coefficients in k,
  evaluates to the original function. This is the node's finite-polynomial meaning
  of generation, without claiming one fixed finite generating list for all c.
- There is no smoothness, connectedness, reducedness, finite-dimensionality, or
  perfection assumption. Universe `u` is explicit and arbitrary; the scheme and its
  base field follow the recorded coordinate and Verschiebung interfaces.

Dependency declarations used (their full signatures and docstrings were read):

- `Mathlib.Algebra.Field.Defs`: `Field` (through the imported dependencies).
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj`, together with
  `CategoryTheory.IsCommMonObj`; the specialization to schemes over Spec k was also
  read in `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`; and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `AlgebraicGeometry.QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Group.Affine`: its canonical global-section Hopf instance,
  the `mathlib_match` of `lem-sfb-affine-group-coordinate-hopf`. The algebra, bialgebra,
  and Hopf instances transport the given scheme operations along the affine equivalence.
  The unbundled-field instance `HopfAction.coordinateHopfAlgebra` from
  `Sheaf.AlgebraicGeometry.HopfCoactionLinearization` is already publicly imported by
  the Verschiebung dependency and exposes this same canonical Mathlib structure.
- `Sheaf.AlgebraicGeometry.AffineGroupFrobeniusVerschiebung`:
  `AlgebraicGeometry.AffineGroupFrobeniusVerschiebung.twist`, `twistAlgebra`,
  `projection`, `iteratedComul`, and the full specifications `Maps`, `GroupMaps`,
  `frobenius_verschiebung`, which identify their composite with the canonical comorphism.
- `Mathlib.RingTheory.Coalgebra.Basic`: `Coalgebra.comul`, `Coalgebra.counit`.
- `Mathlib.Algebra.MvPolynomial.Eval`: `MvPolynomial.aeval`, whose definition evaluates
  coefficients by `algebraMap` and variables at x.

The stated proof-dependency modules are imported without `public`: the additive filtration,
affine extension pushout, Witt extension and its Verschiebung formula, Witt pullback
classification, homomorphism factorization, standard additive group, algebraic closure,
affine closed-immersion criterion, and tensor pushout maps. The naturality-diagonalizable
node currently has neither a Lean record nor a Mathlib match, so there is no recorded
module to import for that proof-only dependency; its role remains explicit in the proof
docstring. It is not required to type this statement. The docstring spells out all nine
proof steps of the accepted DAG proof, including scalar descent and the nonreduced case.

Edge cases checked before writing:

- `n = 0` is permitted: `Fin 0` is empty and a constant multivariate polynomial gives
  a scalar. This includes the trivial group, whose coordinate algebra is k.
- The zero function is the evaluation of the zero polynomial; no nonzero generator
  or nonempty generating list is required.
- The additive group has a primitive coordinate and zero canonical Verschiebung;
  its polynomial algebra is the model case. The same coordinate argument works for
  alpha_p and higher infinitesimal additive kernels, so reducedness is not imposed.
- The constant group Z/p has coordinate presentation k[t]/(t^p-t) with primitive t;
  this checks that disconnected groups have not been excluded.
- In characteristic two the displayed tensor sum remains the primitive condition.
  `Fact p.Prime` includes p=2; it only excludes impossible field characteristics 0 and 1.
- An imperfect field uses the actual Frobenius pushout with second-factor scalars;
  the statement never replaces the twist by C using an inverse field Frobenius.
- An affine group scheme has an identity section, so the empty scheme is not an
  omitted group-scheme case. Finite type does not imply finite-dimensional C, and
  the signature does not assume it.

Searches made on 2026-10-24 using the prescribed msearch.py wrapper:

- LeanFinder: “A commutative affine finite type group scheme with zero Verschiebung
  has coordinate algebra generated by primitive elements”. Eight unrelated hits on
  Weierstrass coordinate rings; no exact statement.
- LeanSearch: “A commutative finite type affine group with zero Verschiebung has
  coordinate algebra generated by primitive functions”. Eight hits, including group
  algebra finite type, Weierstrass coordinates, and WittVector Verschiebung; no match.
- Loogle: `HopfAlgebra, Coalgebra.comul, Algebra.adjoin` returned an unknown-identifier
  error for `Coalgebra.comul`. The corrected quoted query `"HopfAlgebra", "primitive"`
  returned zero hits; absence is not inferred from the failed query.
- Mathlib grep through msearch: `[Pp]rimitive|[Vv]erschiebung` in
  `RingTheory/HopfAlgebra` returned zero hits. Direct rg over Coalgebra, Bialgebra,
  and HopfAlgebra found only the symmetric-algebra primitive-generator comment and
  an unrelated use of “primitive” in coassociativity simplification.
- Direct rg for `primitive|[Vv]erschiebung` and more focused patterns in
  `lean/WeilConjectures` and `lean/Sheaf` found the canonical construction and Witt
  formula modules and unrelated primitive roots/Čech primitives, but no generation
  theorem. Searching the exact node id in `lean/WeilConjectures` found nothing.
- `Algebra.adjoin` was also read as the standard alternative formulation of
  algebra generation. The chosen explicit finite-polynomial conclusion directly
  matches the node's explanatory clause and needs no new predicate for primitives.

Validation: scompile.py compiled this file both as its sandbox module and its final
library module, within the 60-second per-file limit, with no errors or unexpected
warnings. Every variable and universe is explicitly bound; `autoImplicit` is false.
The returned dependency-ownership fault is repaired below; no STATEMENT-DISPUTED issue remains.

## Second reading by Q99

This is a separate self-review, not a claim of review by another agent: the dispatch
brief expressly prohibits starting other agents and reserves independent review to
the maintainer. I reopened the node and finished Lean signature together. The field,
positive characteristic, affine commutative group, and both finite-type components
match one for one. In particular, the hypothesis uses the dependency's actual
projection composed with iterated coproduct and the second-factor scalar structure,
so it is exactly the specified coordinate vanishing and does not silently assume
perfection. The conclusion binds a finite family for each c, tests the coproduct
of every member, and evaluates a k-coefficient polynomial to c. Constants and an
empty family remain admissible. No extra geometric hypotheses, corrected statement,
new node, or duplicate notion was introduced. The return identified the missing direct
coordinate-Hopf ownership dependency; this is now explicitly cited in `stmt_deps`.


## Repair of returned delivery 566b2d63f0ec

H2: added `def-sfb-coordinate-hopf-algebra` to the item’s `stmt_deps`, under
STMT_DEPS MAY GAIN LANDED NODES. I read that landed node’s statement, existing:true
Lean record, and the full `HopfAction.coordinateHopfAlgebra` declaration in
`Sheaf.AlgebraicGeometry.HopfCoactionLinearization`. This definition node owns the
actual unbundled-field Hopf instance used by `Coalgebra.comul`, `Coalgebra.counit`,
and the HopfAlgebra argument of `iteratedComul` in the statement. Its body is the
canonical bundled-base coordinate Hopf instance specialized at `CommRingCat.of k`;
no theorem about coaction linearization is assumed. The public import through
`AffineGroupFrobeniusVerschiebung` already supplies the declaration.

The sandbox node was refreshed from the current read-only main node, retaining the
delivered `lean` record verbatim and adding precisely this dependency. The theorem
module and its signature are unchanged from the returned delivery; no correction
of the mathematical statement, extra node, or dependency-module edit is needed.
The earlier report’s claim that only `lean` changed has been updated accordingly.
The maintainer explicitly found every other mathematical and mechanical clause
correct; this repair addresses the sole returned point.
