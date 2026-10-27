## Worker report

The module `Sheaf.CategoryTheory.ExtOrthogonalAdjointAcyclic` states
`CategoryTheory.acyclic_map_of_coproduct_ext_orthogonal_adjunction`, with one
`sorry` and no new definitions. No node correction, new node, or dependency
repair is needed. There is no released repair note for this item.

Source read: `literature/stacks-project/sites-cohomology.tex`, Tag 07AC,
`lemma-existence-derived-lower-shriek`, especially the proof of condition (2),
lines 9357–9420. The node abstracts exactly its Hom-complex adjunction argument
and injective detection. The proof docstring reproduces all three node steps,
including the explicit kernel/cokernel proof of the injective test.

Hypotheses and clauses, in node order:

- A small site in the common module universe is `{C : Type u} [SmallCategory C]`
  and `J : GrothendieckTopology C`. As in the recorded Hom-acyclicity dependency,
  the sheaf category uses the associated Grothendieck topology, without a choice
  of presentation by coverings. The site and coefficient universe is `u`.
- The commutative ring sheaf is `S : Sheaf J CommRingCat.{u}`. Its underlying ring
  sheaf is `(sheafCompose J (forget₂ CommRingCat RingCat)).obj S`.
- The category A is the recorded `ringedSiteModules.{u}` of that ring sheaf,
  transparently Mathlib `SheafOfModules`, with its existing abelian structure.
- The arbitrary abelian category B has separate object and morphism universes
  `uB`, `vB`, and binders `[Category.{vB} B] [Abelian B] [EnoughInjectives B]`.
  `EnoughInjectives` is exactly the existence of a mono into an injective.
- `L` and `T` have precisely the stated domains and codomains;
  `[L.Additive] [T.Additive]` and `adj : L ⊣ T` record their properties.
  No exactness of L, nor injectivity of T(V), is imposed.
- The family is `E : I → ringedSiteModules ...`, with `{I : Type w}` explicit.
  Any set-indexed family is allowed; every coproduct actually used has its
  index in the fixed common module universe `u`.
- `hExt` quantifies over every `V : B` with `[Injective V]`. It supplies an
  `InjectiveResolution (T.obj V)` whose positive Hom cohomology vanishes for
  every `i : I` and every natural `p > 0`. Positive natural degrees are exactly
  positive integer degrees. This is the node's definition of Ext using an
  injective resolution: `preadditiveCoyoneda.obj (op (E i))` is additive Hom(E_i,-),
  mapped termwise to `Q.cocomplex`, and `IsZero (...homology p)` says its H^p is
  zero. Specifying existence of one such resolution adds no condition: module
  sheaves on this small site have enough injectives, and the computed groups
  are independent of resolution. It avoids introducing a noncanonical chosen
  resolution as a new definition or adding an injectivity hypothesis on T(V).
- `P : CochainComplex (ringedSiteModules ...) ℤ` is the stated cochain complex.
  `hbounded : ∃ b : ℤ, ∀ n : ℤ, b < n → IsZero (P.X n)` is boundedness above,
  without requiring literal equality to a chosen zero object. `hacyclic` is
  exactly `P.Acyclic`.
- `hterms` says for each integer n there exist `A : Type u` and `i : A → I`
  with `Nonempty (P.X n ≅ ∐ (fun a ↦ E (i a)))`. This allows arbitrary small
  coproducts and repetitions, independently in each degree.
- The first conclusion is acyclicity of the termwise complex
  `((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)`.
- The further conclusion quantifies over every injective V and states
  acyclicity of both `HomComplex P ((singleFunctor _ 0).obj (T.obj V))` and
  `HomComplex (L(P)) ((singleFunctor B 0).obj V)`.
- Finally an actual chain isomorphism `e` identifies these Hom complexes.
  `AddCommGrpCat.uliftFunctor` transports their abelian groups to `max u vB`,
  retaining unrestricted vB. The normalization for every integer n and every
  `h : P.X (-n) ⟶ T.obj V` says that `e.hom.f n` sends the cochain represented
  by h to the cochain represented by `(adj.homEquiv (P.X (-n)) V).symm h`.
  Thus e is the specified adjunction identification, not an unspecified
  isomorphism between acyclic objects. Mathlib `Cochain.toSingleEquiv` identifies
  the degree-n term with the indicated Hom group, and `Cochain.δ_toSingleMk`
  gives exactly h ↦ (-1)^(n+1) h∘d^(-n-1), on both sides. Being a chain
  isomorphism includes compatibility with these signed differentials.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `CategoryTheory.Precoverage.IsSiteForCoverings` was read with its full
  signature and source docstring. The site is used through Mathlib
  `GrothendieckTopology`, the associated-topology interface used by the
  recorded Hom-acyclicity theorem and all ringed-site module constructions.
- `def-weil-size-convention` is a metatheoretic convention with no declaration;
  explicit universes u, w, uB, vB and common Hom-universe lifts implement it.
- `Sheaf.CategoryTheory.RingedSiteModules`:
  `CategoryTheory.ringedSiteModules`, the exact transparent SheafOfModules
  abbreviation. Its full definition and the underlying Mathlib structure
  and morphisms in `Mathlib.Algebra.Category.ModuleCat.Sheaf` were read.
- `Mathlib.CategoryTheory.Abelian.Basic`: `CategoryTheory.Abelian`.
- `Mathlib.CategoryTheory.Preadditive.Injective.Basic`:
  `CategoryTheory.Injective`, `CategoryTheory.EnoughInjectives`.
- `Mathlib.CategoryTheory.Preadditive.Injective.Resolution`:
  `CategoryTheory.InjectiveResolution`, including cocomplex, degreewise
  injectivity, augmentation and quasi-isomorphism fields.
- `Mathlib.Algebra.Homology.HomologicalComplex`: `CochainComplex`.
- `Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex`:
  `HomologicalComplex.Acyclic`, exactness in every degree.
- Proof dependency `Sheaf.CategoryTheory.AcyclicCoproductExtOrthogonalHom`:
  `CategoryTheory.acyclic_hom_of_coproduct_ext_orthogonal`. Its full signature
  and proof docstring were read. It supplies exactly the same module category,
  positive Hom-resolution cohomology, boundedness, termwise coproduct condition,
  and signed HomComplex convention; it is a non-public proof import.
- `Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle`:
  `CochainComplex.HomComplex`, `Cochain.toSingleMk`, `Cochain.toSingleEquiv`,
  and `Cochain.δ_toSingleMk`.
- `Mathlib.CategoryTheory.Adjunction.Additive`: the additive adjunction API,
  in particular `Adjunction.homAddEquiv` and its universe-lifted Yoneda
  comparison, was read to verify the canonical additive identification.

Edge cases checked before writing: the family may be empty (then the term
coproducts are zero); the summand index in each degree may be empty; the
index map need not be injective (repetitions); P may be zero and may be
unbounded below; its upper bound may be any integer. The Ext condition starts
at p=1 and does not impose vanishing of Hom in degree zero. Hom-complex
conclusions cover every integer degree, including zero and negative degrees.
No nonempty-family, nonzero-object, bounded-below or exact-left-adjoint
hypothesis appears. Different morphism universes for A and B are permitted.

Searches (all through prescribed tools or the permitted source directories):

- msearch LeanFinder, query “An additive adjunction transfers bounded above
  acyclicity for complexes of coproducts of Ext orthogonal objects by testing
  Hom complexes against injectives”: 8 hits, chiefly injective-dimension and
  K-injective/K-projective orthogonality. None states this preservation result.
- msearch Loogle, query `"HomComplex", "Adjunction"`: 0 hits.
- msearch LeanSearch, query “If Hom from a complex into every injective is
  acyclic then an additive adjoint image complex is acyclic”: 8 hits, chiefly
  `HomologicalComplex.Acyclic`, `acyclic_iff`, and K-injective orthogonality.
  None states this result for a possibly nonexact left adjoint.
- msearch grep in Mathlib `Algebra/Homology`, query
  `[Aa]cyclic.*[Ii]njective|[Ii]njective.*[Aa]cyclic|[Ee]xt.*orthogonal`:
  3 hits, all in KInjective.lean; none is the required theorem.
- rg in `lean/WeilConjectures` and `lean/Sheaf`, query
  `ext.orthogonal|ext_orthogonal|HomComplex.*[Aa]djunction|homComplex.*[Aa]djunction`:
  found the recorded `acyclic_hom_of_coproduct_ext_orthogonal` and a specialized
  extension-from-a-point comparison, `WeilConjectures.PointDerivedHom`.
  Neither states this generic adjunction transfer. The point comparison source
  was opened and checked; its specific site, scalar and functor assumptions
  do not provide the present arbitrary-site/category statement.
- rg for the item id in `lean/WeilConjectures`: no declaration.
- rg for `acyclic_map_of_coproduct_ext_orthogonal_adjunction` in Mathlib,
  `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`:
  no existing declaration or name collision.

Validation: prescribed scompile.py compiled the final module in both sandbox
and library positions, cleanly, within 4 seconds per compile. The final
expected theorem proof remains `sorry`; no proof has been supplied.

## Second reading by Q22

A separate rereading in this worker session compared the node, source, and
complete Lean signature clause by clause; no additional agent was started,
following the dispatcher instruction. The maintainer's independent review
will read this delivery separately. The check found no omitted or additional
mathematical hypothesis. In particular, hExt is a resolution computation of
Ext, not an assumption that the right adjoint preserves injectives; hterms
permits empty sums and repetitions; the result asserts both Hom acyclicity
clauses and the image complex's acyclicity. The normalized chain isomorphism
records the actual adjunction on every term. Lifts are solely coefficient
universe transport and do not narrow B. No changes resulted from this rereading.
