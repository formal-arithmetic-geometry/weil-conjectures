## Worker report

The module Sheaf.AlgebraicGeometry.DiagonalizableRepresentationWeightGrading states
AlgebraicGeometry.DiagonalizableRepresentation.weightGrading. Its only theorem proof
is `sorry`; every helper contains actual data. The module's theorem docstring carries
all nine proof steps, including coefficient extraction, both inverse sum maps and the
universal A[M]-point argument. No statement is disputed or corrected.

Hypotheses and clauses, with namespace DiagonalizableRepresentation understood:

- Field k: `{k : Type u} [Field k]`. Additive abelian M: `{M : Type u}
  [AddCommGroup M]`; finite generation: `[AddGroup.FG M]` on weightGrading.
  No torsion-free, characteristic-zero, algebraically-closed or reducedness assumption.
- k[M], its Hopf maps and D_k(M): use the landed `diagonalizableGroup k M`,
  whose definition is hopfSpec of `CommHopfAlgCat.of k (AddMonoidAlgebra k M)`.
  Its coproduct, counit and antipode are the canonical group-algebra ones.
  Added the already-landed definition node def-sfb-diagonalizable-group to stmt_deps.
  No new node or copied definition of D(M).
- Character chi_m: `characterValue m A x` is
  `(Spec.mapMulEquiv.symm x).ofConv (AddMonoidAlgebra.single m 1)`.
  This is exactly evaluation of e_m under the algebra map of the point x, hence the
  point formula for the character dual to t maps to e_m. Its scalar value is used;
  there is no arbitrary character or extra character hypothesis.
- Finite-dimensional V: `{V : Type u} [AddCommGroup V] [Module k V]
  [FiniteDimensional k V]`. Fix the existing `RationalRepresentation.finiteBasis`;
  this is a general finite basis, not a weight basis. `Representation` abbreviates
  the existing `GeneralLinearGroup.RationalHom` on this finite index. Thus rho is an
  actual morphism of schemes to GL(V); `[IsMonHom rho]` is precisely the group law.
  Transport along a fixed basis loses and adds no representations.
- GL(V)(A) and rho_A: `pointAction rho A x` composes the point x with rho, applies
  `GeneralLinearGroup.homMulEquiv`, and transports the invertible matrix through
  `Matrix.GeneralLinearGroup.toLin'` in `finiteBasis.baseChange A`. Its result is
  an A-linear automorphism of `A ⊗[k] V`. This is the symmetric tensor convention
  A tensor V rather than V tensor A; chi_m(x) tensor v corresponds to v tensor chi_m(x).
- V_m: `weightSpace rho m` is the intersection over every A, CommRing A, Algebra k A,
  and x in D(M)(A), of the equalizers of rho_A(x) composed with v maps to 1 tensor v
  and v maps to chi_m(x) tensor v. Membership unfolds exactly to the node's displayed
  equation with no rational-point restriction. LinearMap.eqLocus supplies submodules.
- Finite nonzero weights: `{m : M | weightSpace rho m ≠ ⊥}.Finite`.
- Original decomposition: `Function.Bijective (weightSum rho)`, where weightSum is
  exactly `DirectSum.coeLinearMap (weightSpace rho)`. A bijective linear map is an
  isomorphism of vector spaces. Naming it avoids adding DecidableEq M as a hypothesis.
- For every A: `Function.Bijective (sumMap rho A)`. The domain is
  `DirectSum M (fun m ↦ A ⊗[k] weightSpace rho m)`, and its component maps are the
  actual `summandMap rho A m = (weightSpace rho m).subtype.baseChange A`.
  This explicitly specifies the canonical base-change sum isomorphism. Its
  bijectivity also implies injectivity of each component inclusion.
- Scalar action: for every A, m, x and z in A tensor V_m, the next conjunct says
  `pointAction rho A x (summandMap rho A m z) =
   characterValue m A x • summandMap rho A m z`.
  The universal quantifier over algebras includes every commutative A-algebra B,
  with the composite k-structure; D(M)_A(B)=D(M)(B), and the canonical cancellation
  identifies extension from A to B. Thus this is the group-scheme scalar-action
  clause, including further extensions, not only the assertion at one algebra.
- Commutant: for every A-linear f, the premise quantifies over every B with
  `[CommRing B] [Algebra k B] [Algebra A B] [IsScalarTower k A B]` and every
  x in D(M)(B). `extendEnd A B f` is f.baseChange B conjugated by the actual
  `TensorProduct.AlgebraTensorModule.cancelBaseChange k A B B V` equivalence.
  Equality of the two linear-map composites states precisely commutation.
  The conclusion is `Set.MapsTo f (summandMap rho A m).range
  (summandMap rho A m).range` for each m, i.e. preservation of every summand.

All objects and test algebras lie in a common arbitrary universe u, as in the
recorded representation dictionary and existing scheme/matrix APIs. This does not
impose countability or finiteness on algebras: u may be any containing universe.
In particular it contains k[M] and A[M], which detect weights and commutants.

Dependency declarations read and reused:

- Mathlib.Algebra.Field.Defs: Field.
- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Spec and Spec.map.
- Mathlib.CategoryTheory.Monoidal.Grp: CategoryTheory.GrpObj, IsMonHom via the
  upstream group-scheme API; not a separate notion of group scheme.
- Sheaf.AlgebraicGeometry.StandardGroupSchemes: multiplicative and
  multiplicativeGroup (the Laurent Hopf model of G_m).
- Sheaf.AlgebraicGeometry.LinearGroupSchemes and upstream
  WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear: GeneralLinearGroup,
  GeneralLinearGroup.homMulEquiv; GeneralLinear.Lie: RationalHom. The recorded
  LinearGroupSchemes module explicitly reuses this GL and supplies SL, not a new GL.
- Mathlib.LinearAlgebra.FiniteDimensional.Defs: FiniteDimensional = Module.Finite.
- Mathlib.LinearAlgebra.TensorProduct.Defs: TensorProduct; Tower: LinearMap.baseChange
  and AlgebraTensorModule.cancelBaseChange, whose full signatures and formulas were read.
- Mathlib.Algebra.DirectSum.Module: DirectSum, toModule and coeLinearMap, matching
  the recorded direct-sum module definition and its canonical finite-family sum.
- Sheaf.AlgebraicGeometry.DiagonalizableGroup: diagonalizableGroup (landed definition).
- Proof dependency Sheaf.AlgebraicGeometry.RationalRepresentationComoduleDictionary:
  NaturalRepresentation, genericPoint, coordinatePoint, genericCoaction,
  CoordinateComodule, dictionary and finite_dictionary; finiteBasis and FiniteIndex
  are used directly to realize the arbitrary V. The complete module was read.
- Proof dependency Mathlib.AlgebraicGeometry.Morphisms.FiniteType:
  LocallyOfFiniteType and QuasiCompact. All recorded proof-dependency modules are imported.

Edge cases checked mathematically against the definitions:

- M=0: k[M]=k, only weight zero, V_0=V, both sum maps are the canonical unit identifications.
- V=0: finiteBasis has empty index and the genuine GL_0 is trivial; all weight spaces
  and scalar extensions are zero. The sum maps are bijective between zero modules.
- A=0 (and B=0): allowed by CommRing without Nontrivial; tensor modules and actions
  are zero and all asserted equations hold.
- M with characteristic-p torsion, e.g. Z/p in characteristic p: D(M)=mu_p is
  nonreduced, but e_m are still a formal basis. All-algebras equalizers and the
  universal point retain these distinct weights; no differentiation or k-point
  separation is used. M may also have torsion prime to p or an infinite free part.
- Arbitrary nonreduced A and nonflat A-to-B maps: no flatness hypothesis was added;
  direct-sum inverses are obtained by extending the coefficient projections.

Sources inspected: Milne iAG2017, printed pp.234--235 (PDF pages 246--247),
Theorem 12.12(a) implies (b) and (d), Remark 12.13 and its all-algebras formulation;
current literature/blueprint/latest unit sk-thm-sf-ctf-stability and its direct-images
proof (3), serving the central-diagonalizable weight-block argument in the node ancestry.

Searches actually run with msearch.py Q41 and this item:

- leanfinder: “A representation of a diagonalizable group scheme is the direct sum of
  finitely many character weight spaces, compatible with scalar extension and
  equivariant endomorphisms”: OK 8 hits, Rep.diagonal, diagonalHomEquiv and related
  abstract-group diagonal representation lemmas. None states the scheme result.
- loogle: `"Comodule", "DirectSum"`: OK 0 hits.
- grep: `diagonalizable|diagonalisable|weightSpace|weight_space`: OK 25 hits, ordinary
  diagonalizability and Lie weight spaces, not arbitrary diagonalizable group schemes.
- rg in lean/WeilConjectures for the same patterns: only Lie weight-space material;
  grep for the item id: no hit. Name search for DiagonalizableRepresentation and
  weightGrading in Sheaf: no clash. Sheaf searches found GmRepresentationWeightBasis
  (M=Z only), TorusCharacterTangentWeights (adjoint torus weights) and the existing
  DiagonalizableGroup and representation dictionary, which are reused. No exact
  theorem or one-line specialization includes arbitrary torsion M and all the clauses.

Validation: scompile.py compiled both sandbox and library module cleanly (5.1 s and
3.2 s respectively). autoImplicit is false; there are no temporary #check commands,
local notation, local instances, private definitions, or lines over 100 characters.

## Second reading by Q41

I reread the completed module against every hypothesis and clause above. The dispatcher
forbids starting other agents, so this is a worker self-check, not a claim of independent
review; the maintainer's independent review reads this delivery. Checked particularly:
weightSpace quantifies over all algebras; rho is an actual scheme map, not arbitrary
endomorphisms; sumMap uses the actual inclusions; extendEnd transports along the canonical
tensor cancellation; range preservation is precisely the commutant conclusion. No mathematical
statement mismatch was found. Compiler repairs replaced the old Finsupp representation of
the additive group algebra by AddMonoidAlgebra.single and made all direct-sum binders explicit.
No additional hypotheses or clauses resulted from those repairs.
