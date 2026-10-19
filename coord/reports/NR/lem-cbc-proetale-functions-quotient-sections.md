## Worker report

The module `Sheaf.AlgebraicGeometry.ProEtaleFunctionsQuotientSections` states
`AlgebraicGeometry.Scheme.exists_proEtale_functions_quotient_sections`, with exactly
one theorem and a `sorry` proof. No definitions, auxiliary axioms, new nodes, or
statement corrections are introduced.

Source read: Stacks `proetale.tex`, Example
`example-functions-mod-locally-constant-functions` (Tag 0F6D), especially the
short exact sequence, closed-point/separably-closed hypotheses, H1 vanishing,
and final affine quotient display. The DAG proof's six steps are reproduced in
the theorem docstring. The read-only framework note
`coord/pefw-upstream-framework.md` and the side framework site declarations were
consulted; no alternative site or constant-sheaf notion is introduced.

Hypothesis and clause correspondence:

- An arbitrary scheme is `X : Scheme.{u}`; an arbitrary abelian group is
  `A : Type (u + 1)` with `[AddCommGroup A]`. The site is `X.ProEt` with
  `ProEt.topology X`. Coefficients and sections are in its ambient value universe,
  following the existing constant-sheaf/site convention, without finiteness,
  nonemptiness, torsion, or characteristic assumptions.
- The all-functions presheaf being a sheaf is stated by existence of an actual
  `F : Sheaf (ProEt.topology X) AddCommGrpCat` and additive identifications
  `e V : F.obj.obj (op V) ≃+ (V.left → A)`. The first conjunct says every
  restriction is precomposition with the underlying scheme map `f.left`.
  These data identify F with exactly the specified functions presheaf, rather
  than merely claiming a sheaf with abstractly isomorphic groups of sections.
  This existential presentation makes no data definition from a sorried theorem.
- The constant sheaf is the recorded Mathlib `constantSheaf`, applied to
  `AddCommGrpCat.of A`. Its inclusion is `i`, with `Mono i` explicitly asserted.
  The equation using `toSheafify` says the constant presheaf section `a`
  maps to the constant function `a`. The next equivalence says the image on
  every object is precisely `IsLocallyConstant f`, so i is the inclusion induced
  by locally constant functions. No discreteness structure on A is needed.
- The quotient sheaf is Mathlib's `cokernel i` in the abelian sheaf category.
  The existential isomorphism `c` identifies it with
  `(presheafToSheaf ...).obj (cokernel i.hom)`. Its displayed equation identifies
  the two quotient projections after the sheafification unit. Thus the
  presheaf-cokernel/sheaf-cokernel clause includes the canonical maps.
- The assumptions on X occur only in the final implication: closedness is
  `∀ x : X, IsClosed ({x} : Set X)` and separable closedness is
  `∀ x : X, IsSepClosed (X.residueField x)`. They do not restrict the preceding
  sheaf and monomorphism assertions, which apply to every scheme.
- Every affine object is quantified as `∀ V : X.ProEt, IsAffine V.left → ...`.
  The subgroup LC is Mathlib's
  `(LocallyConstant.coeFnAddMonoidHom : LocallyConstant V.left A →+ (V.left → A)).range`.
  Its elements are exactly the functions constant on an open neighbourhood of
  each point. The equivalence `q` is an additive equivalence from the displayed
  quotient to `(cokernel i).obj.obj (op V)`; taking its inverse gives the direction
  written in the node. The final equation on every function class forces q to
  be induced by `cokernel.π i`. It determines q uniquely because the group
  quotient projection is surjective, and gives compatibility with restrictions
  between affine objects from naturality of that cokernel projection and e.

Dependency declarations used, read with their signatures and docstrings:

- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`: recorded site dependency
  `AlgebraicGeometry.Scheme.proEtaleDerivedCategory`; its public site interface
  is Mathlib `AlgebraicGeometry.Scheme.ProEt` and `ProEt.topology`. The derived
  category itself is not a notion required in this statement.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`.
- `Mathlib.CategoryTheory.Sites.Sheafification`: `CategoryTheory.presheafToSheaf`,
  `CategoryTheory.toSheafify`, `CategoryTheory.sheafificationAdjunction`.
- `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`: the recorded abelian
  sheaf/cohomology framework, including `CategoryTheory.Sheaf.H'`; the statement
  uses its `CategoryTheory.Sheaf` category and Mathlib cokernels, not H1 itself.
- `Mathlib.FieldTheory.IsSepClosed`: `IsSepClosed`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and scheme Hom.
- `Mathlib.AlgebraicGeometry.ResidueField`: `AlgebraicGeometry.Scheme.residueField`,
  whose carrier is the quotient of the local stalk by its maximal ideal.
- `Mathlib.Topology.LocallyConstant.Algebra`: `LocallyConstant.coeFnAddMonoidHom`.
  Mathlib's quotient group supplies `QuotientAddGroup.mk`.

The stated proof-dependency modules already recorded are imported as proof imports:
`Mathlib.AlgebraicGeometry.Morphisms.Flat`,
`Sheaf.CategoryTheory.Sites.CohomologyOverObjectLocalization`, and
`Sheaf.CategoryTheory.Abelian.RightDerived.FullLongExactSequence`.
The other proof dependencies have no available Lean record in the DAG snapshot;
they are named in the proof plan and are not substituted by invented declarations.

Edge cases checked: the empty scheme and empty affine object are allowed; all
functions on an empty space form the zero group and so does their quotient.
On empty objects the constant presheaf unit may identify different constants;
the theorem does not wrongly assert injectivity of that unit. The zero group A
is allowed and yields zero quotient. Nontrivial finite discrete spaces have only
locally constant functions and hence zero quotient. No discrete topology on X,
no Noetherian condition, and no characteristic restriction is imposed. Pointwise
closedness does not mean discreteness and is rendered by singleton closedness.

Searches actually run:

- msearch leanfinder: `The proetale sheaf of all functions modulo locally constant
  functions has affine sections the quotient group`. Eight hits about affine
  transition limits, module tilde sections, and the etale locus; no match.
- msearch loogle: `"LocallyConstant", "Sheaf"`. Twelve hits in condensed/light
  condensed locally constant presheaves; none asserts this scheme-site quotient.
- msearch leansearch: `sheaf of all functions modulo locally constant functions`.
  Service unavailable (Internal Server Error), recorded as unavailable.
- msearch grep: `locallyConstant.*cokernel|functions.*quotient|ProEt.*function`.
  Five unrelated hits (Euclidean domains, Lie groups, uniform separation,
  complex open mapping and type quotients); no match.
- rg in both source checkouts for functions presheaves, continuous-map sheaves,
  ProEt constant/functions and quotient-functions names. The existing continuous
  map presheaf and small-etale constant-sheaf comparison do not assert this
  pro-etale quotient formula. The exact node-id search in slopmaster2 returned
  no match. `rg` in `lean/Sheaf` and `dag/lean_names_upstream.json` found no matching
  quotient declaration; unrelated formal-functions modules were inspected as
  irrelevant search results. The side framework `Sites/Proetale.lean` supplies
  the site, but no functions-quotient statement.

Server compilation via scompile.py succeeded cleanly (2.3 seconds, nice 19,
two threads, 60 seconds per file). No local compiler was invoked.

## Second reading by NR

I independently read the node's statement and six proof steps, Stacks
`proetale.tex` lines 4238–4266 (Example 0F6D), the delivered Lean, all seven
statement-dependency records, their relevant declarations, and the recorded
proof interfaces. The example starts afresh with an arbitrary scheme and
abelian group; it inherits no Noetherian, characteristic, or finite-coefficient
assumption from surrounding results. The source's assertion about non-pullback
when A has more than one element is outside this node, so is correctly omitted.

Object/hypothesis/conclusion checklist, with Lean correspondence and verdict:

1. Arbitrary scheme X and abelian group A: `(X : Scheme.{u})`,
   `(A : Type (u + 1)) [AddCommGroup A]`. PASS: no additional algebraic,
   topological, finite, or nonzero assumptions on A.
2. Small pro-etale site and its arrows: `X.ProEt`, `ProEt.topology X`,
   `f : U ⟶ V`, `f.left`. PASS: I opened the recorded module
   `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`, Mathlib's actual
   `ProEt := MorphismProperty.Over @WeaklyEtale ⊤ X`, and the exact side
   framework `WeilConjectures/Mathlib/AlgebraicGeometry/Sites/Proetale.lean`.
   They use weakly etale objects and the fpqc/pro-etale topology, not the
   small etale site or arbitrary jointly surjective covers. I also read
   `coord/pefw-upstream-framework.md`.
3. All point functions, with pointwise abelian operations, form a sheaf:
   existential `F : Sheaf ... AddCommGrpCat` and additive equivalences
   `e V : F.obj.obj (op V) ≃+ (V.left → A)`. PASS: the first conjunct
   identifies every restriction with precomposition by `f.left`, so this
   is precisely the specified presheaf up to natural additive isomorphism.
4. The constant abelian sheaf: `(constantSheaf ...).obj (AddCommGrpCat.of A)`.
   PASS: I read Mathlib's definition as constant presheaf followed by
   `presheafToSheaf`, not a presheaf of constant global values.
5. Locally constant functions induce its inclusion: existential `i`, `Mono i`,
   the equation on `toSheafify` of each constant a, and the image equivalence
   with `IsLocallyConstant f`. PASS: the constant equation determines the
   morphism through the sheafification universal property; the image clause
   identifies its sectionwise range, without asserting a false injection of
   constant-presheaf sections on the empty object.
6. Quotient in abelian sheaves, equivalently sheafified presheaf cokernel:
   `cokernel i` and `∃ c : (presheafToSheaf ...).obj (cokernel i.hom) ≅
   cokernel i`. PASS: the equation for c identifies the quotient projections,
   so the comparison includes the specified canonical maps.
7. Every singleton of X is closed and every residue field separably closed:
   `(∀ x : X, IsClosed ({x} : Set X)) →
   (∀ x : X, IsSepClosed (X.residueField x)) → ...`. PASS: these occur only
   in the final implication, and singleton closedness does not impose a
   discrete topology. I read the residue-field definition as
   `IsLocalRing.ResidueField (X.presheaf.stalk x)` and the polynomial-splitting
   definition of `IsSepClosed` in the dependency sources.
8. Every affine object V: `∀ V : X.ProEt, IsAffine V.left → ...`. PASS:
   neither V's structural map nor X is required to be affine.
9. Canonical additive quotient formula: q identifies the quotient of
   `(V.left → A)` by the range of `LocallyConstant.coeFnAddMonoidHom` with
   `(cokernel i).obj.obj (op V)`. PASS: that range is exactly the subgroup
   of locally constant point functions, using Mathlib's bundled locally
   constant maps and pointwise additive operations. The equation for every f
   specifies q as the map induced by the cokernel projection through e.
   Its inverse is the direction in the node; naturality of e and the
   projection gives compatibility between affine objects. No clause is lost.

Edge cases: the empty scheme, empty affine object, and zero coefficient group
are all permitted. All functions on the empty object form the zero group;
the locally constant subgroup and quotient do too. There is no nonemptiness
binder or asserted injectivity of A into sections on an empty object. Finite
discrete affine spaces give zero quotient since every function is locally
constant. Closed points need not be open, so nondiscrete examples remain
included. No index type or n is introduced, hence no empty-index or n=0
restriction arises. All characteristics are allowed. The site is made from
u-sized schemes, with coefficients and values in the ambient universe u+1;
this follows the dependency's universe convention and permits arbitrary
coefficient size by increasing the ambient universe. Every variable and
universe is bound explicitly; no extra typeclass hypothesis appears.

Independent searches (different queries from the first worker):

- msearch leanfinder: `Abelian sheaf of arbitrary point functions on a scheme
  and quotient by the constant subsheaf`. Eight hits, about module sheaves,
  structure-sheaf sections, and module global sections; none is this assertion.
- msearch loogle: `"cokernel", "constantSheaf"`. Zero hits.
- msearch grep: `constantSheaf.*cokernel|cokernel.*constantSheaf|functions_quotient_sections`.
  Zero hits.
- Direct rg across Mathlib's algebraic-geometry/sites sources, both project's
  Lean roots and slopmaster2's WeilConjectures for point functions, functions
  sheaves and locally-constant cokernels: no matching theorem. The existing
  continuous-map fpqc sheaf theorem in Mathlib/AlgebraicGeometry/Sites/ConstantSheaf
  is a genuine proof input, not the full quotient theorem. I opened its
  `continuousMapPresheafAb` construction and `isSheaf_fpqcTopology_continuousMapPresheafAb`
  signature: no separation assumption is imposed on the coefficient topology.
  Existing finite locally constant kernel/cokernel results do not state this
  arbitrary-coefficient, all-point-functions quotient result.

Mismatch repaired: the first worker cited the continuous-functions fpqc
sheaf theorem in proof step 1 but omitted its module from the proof imports.
I added `import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf`, as required
by the stage-2 proof-dependency import rule. The mathematical signature,
node statement, and node Lean record were already correct and are unchanged.
No new definition node or dependency module is needed; there is no statement
correction or citer verdict to audit. There is one public named theorem,
its entire proof is `sorry`, and there are no definitions, axioms, private
helpers, local notation or local instances. Both source/blueprint docstrings
are present; all six proof steps and their dependencies are retained.
The signature equals `lean.statement` verbatim and every source line is at
most 100 characters.

Second-reader compilation: scompile.py compiled the delivered module cleanly
on the server in 2.4 seconds, nice 19, two threads, 60-second file limit.
No local compiler or global build was invoked.
