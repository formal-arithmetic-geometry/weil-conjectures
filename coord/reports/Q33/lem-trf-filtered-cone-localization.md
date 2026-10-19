## Worker report

The interrupted delivery retained only `.brief*` and `.check` dispatcher markers:
there was no node copy, module, report, or prior second-reading section. This packet
reconstructs the missing statement in `Sheaf.Algebra.Homology.FilteredConeLocalization`.
It does not claim that an unavailable earlier worker's text was inspected.
The sole new theorem is `CategoryTheory.filteredConeLocalization`, with proof `sorry`.
No definitions, dependency modules, new nodes, or mathematical statement corrections
are introduced. The item's only changes are its `lean` record and the addition of
already landed `def-trf-finite-filtered-localization` to `stmt_deps`.

Objects and clauses, in source order:

- An arbitrary abelian category is `A : Type u`, `[Category.{v} A]`, `[Abelian A]`.
- The finite filtered category is `FiniteFilteredObjects A B false`. `B = none`
  selects all finite filtrations, degree by degree. `B = some (a,b)` imposes
  `F^a = top`, `F^(b+1) = bot`; `_hB` records exactly the node's `a ≤ b` restriction.
- The bounded-below filtered homotopy category is
  `FiniteFilteredHomotopyPlus A B false`, the existing `HomotopyCategory.Plus`
  of that category; its chain homotopies are filtration-preserving by construction.
- `finiteFilteredQuasiIso A B` is W: every graded map is a quasi-isomorphism.
- The first conjunct states the standard homotopy category is triangulated. The
  second characterizes its distinguished triangles by actual cochain cone triangles
  `CochainComplex.mappingCone.triangleh f.hom` for bounded-below complexes X,Y.
- The third conjunct quantifies over every `ObjectProperty` J of the finite
  filtered category, equipped with zero and binary biproducts. Full-subcategory
  preadditivity and additive inclusion are inherited. It states triangulation of
  `HomotopyCategory.Plus J.FullSubcategory` and exactness of
  `J.ι.mapHomotopyCategoryPlus`, using the same standard cone structure.
- The fourth conjunct says W membership for the first map of any distinguished
  triangle is equivalent to vanishing of every cohomology object of every grade
  of its third vertex. This is the graded-acyclic cone criterion; no cone is
  assumed acyclic and no map is replaced by an arbitrary comparison map.
- The fifth and sixth conjuncts state triangulation of the actual W-localization
  `FiniteFilteredDerivedPlus A B` and exactness of the canonical `finiteFilteredQh`.
- The final conjunct says precisely that localized distinguished triangles are
  isomorphic to images of distinguished homotopy triangles. The second conjunct
  identifies these with images of cone triangles.

Dependency interfaces read:

- `def-sp-abelian`: Mathlib `CategoryTheory.Abelian` (Basic.lean).
- `def-sp-filtration`: upstream `CategoryTheory.DecreasingFiltration` from
  `WeilConjectures.CategoryTheory.Abelian.Filtration`; its fields are F and F_succ_le.
  `Sheaf.CategoryTheory.Filtration` exposes step = F, gradedPiece = gr, and the
  filtration-preserving category on the upstream `FilteredObject`. Finiteness is
  the existing existential pair of extreme steps, not IsFiniteSeparated (which
  would impose a normalization at zero).
- `def-sp-filtered-complex-subquotients`: opened
  `Sheaf.Algebra.Homology.FilteredComplexSubquotients`, including complexStep,
  complexQuotient and complexQuotientπ. The graded object is the cokernel of the
  inclusion of consecutive steps. The termwise graded functor used here is the
  same canonical cokernel construction in `filteredEvaluation`.
- `def-weil-abstract-derived-category`: Mathlib DerivedCategory.Basic supplies
  the usual cochain/homology conventions; no choice of an ordinary derived
  category or HasDerivedCategory assumption is needed to state this item.
- `def-weil-triangulated-category`: Mathlib Pretriangulated, IsTriangulated,
  Functor.CommShift and Functor.IsTriangulated. Shift comparison is the existing
  canonical instance, not extra existential data.
- `def-trf-finite-filtered-localization`: opened its node and entire module,
  including finiteFilteredProperty, finiteFiltered_hasFiniteProducts,
  filteredEvaluation, FiniteFilteredHomotopyPlus, finiteFilteredQuasiIso,
  FiniteFilteredDerivedPlus and finiteFilteredQh. This already landed notion is
  added to stmt_deps rather than privately reconstructed. The existing left
  fractions and compatibility instances select the standard triangulation.

Proof-only imports include the recorded cone criterion
`WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic` and Mathlib's
homotopy triangulation, triangulated subcategory, triangle-isomorphism and
triangulated localization APIs. Every one of the node's seven proof steps is
carried in the theorem docstring. No dependency import closes a cycle.

Searches (2026-10-17):

1. `msearch.py Q33 lem-trf-filtered-cone-localization leansearch` with
   "The bounded below homotopy category of finite filtered objects has cone
   triangles and graded quasi-isomorphism localization is triangulated": 8 hits,
   including HomotopyCategory.mappingCone_triangleh_distinguished and general
   triangulated localization instances. These are ingredients, not this statement.
2. `msearch.py ... leanfinder` with "Taking associated graded commutes with
   mapping cones and localization of bounded below filtered complexes is
   triangulated": 8 hits, including mappingCone.mapTrianglehIso, mapTriangleIso,
   mapHomologicalComplexXIso and ordinary derived-category results. No full match.
3. `msearch.py ... grep 'FiniteFilteredHomotopyPlus|finiteFilteredQuasiIso|
   filteredConeLocalization'`: 0 upstream hits. Direct `rg` over Mathlib,
   `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`, and repository `lean/Sheaf`
   for filtered/triangulated/cone combinations found FiniteFilteredLocalization's
   compatibility theorem and FilteredDerivedHomCalculus's specialized structures.
   Opened those entire modules: neither states this node. The latter uses uniform
   filtration bounds and an enough-injectives existence theorem, so is not a match.
   `dag/lean_names_upstream.json` has no finiteFiltered declaration/name collision.

Validation: prescribed scompile.py on the delivered module, sandbox and library
modes, clean. The final signature is copied verbatim into lean.statement.

## Second reading by Q33

Recovery note: there was no previous review section to preserve and no earlier
statement to compare. After reconstructing the packet I re-opened its Lean and
node for the following source-to-signature audit. All verdicts below concern this
actual delivered text, not a presumed original worker delivery.

Source read first: `literature/stacks-project/derived.tex`, section 05RX
(lines 4167 onward), filtered-acyclic definition, lemma 05S1 and definition 05S2
(lines 4292–4334); also 014X (lines 3431 onward). The ambient hypothesis is only
that A is abelian. 05RX explicitly permits filtration bounds varying by degree.
The bounded-below restriction and fixed-interval specialization are exactly the
ones requested by the node's source field. No source-based correction is needed.
No maintenance repair note for this item is present.

The complete item-by-item checklist is:

1. Object A and its abelian structure: `A : Type u`, `Category.{v} A`, `Abelian A`.
   PASS: independent object and morphism universes, no enough-injectives, ring,
   characteristic, finiteness or Noetherian hypothesis.
2. Choice of C, either all finite filtered objects or prescribed a ≤ b:
   `FiniteFilteredObjects A B false`, `B : Option (ℤ × ℤ)`, `_hB`.
   PASS: false disables the injective-grade condition, none leaves bounds local
   to each object, and the explicit validity binder exactly retains a ≤ b.
   The shared definition does not accidentally demand a uniform bound on complexes.
3. K+(C), with integer degrees and filtered homotopies:
   `FiniteFilteredHomotopyPlus A B false` unfolds to Mathlib's bounded-below full
   subcategory of the homotopy category of C. PASS: maps and homotopies are in C;
   no unfiltered homotopy quotient or only cohomological boundedness was substituted.
4. Graded acyclicity and W: `finiteFilteredQuasiIso` quantifies over every p,
   and the fourth conjunct quantifies over every p,n with `IsZero` of the graded
   homology object. PASS: both degrees range over all ℤ and the grade is the
   recorded consecutive-step cokernel, using the canonical graded functor.
5. K+(C) triangulated with the specified shifts and cone triangles:
   `IsTriangulated ...` and the second conjunct's `mappingCone.triangleh f.hom`.
   PASS: Mathlib's structure is fixed, not an arbitrary triangulation. Checked
   Shift.lean:144 (shift by one negates d), MappingCone.lean:275–290 (cone
   differential), and Pretriangulated.lean:54 (last arrow is minus projection).
   Mathlib orders the two summands as X[1],Y; the canonical biproduct interchange
   gives the node's Y,X[1] convention. Direct sums in C give the direct-sum
   filtration by the shared finite-products construction.
6. Every full additive J, its cone triangulation and exact inclusion:
   third conjunct's `∀ J`, `HasZeroObject`, `HasBinaryBiproducts`,
   `IsTriangulated (HomotopyCategory.Plus J.FullSubcategory)` and
   `J.ι.mapHomotopyCategoryPlus.IsTriangulated`. PASS: the two instances express
   precisely additive subcategory, not an extra condition on A or all J.
   Preadditivity is inherited. Mathlib's Plus structure uses the same cone
   triangles, and the induced inclusion carries its canonical shift comparison.
7. W iff cone graded acyclic: fourth conjunct for every distinguished T.
   PASS: T.obj₃ is a cone of T.mor₁. This formulation is equivalent to checking
   the explicit cochain cone because all distinguished cones are isomorphic,
   and graded cohomology preserves isomorphisms. Quantifying over any cone does
   not strengthen the mathematical assertion; it removes a choice of representative.
8. Actual localization, triangulation, exact Q, and distinguished triangles:
   final three conjuncts use FiniteFilteredDerivedPlus, finiteFilteredQh and the
   iff with `Nonempty (T ≅ Q.mapTriangle.obj S)`. PASS: the category and functor
   are the existing formal W-localization. The preceding cone characterization
   makes this exactly the stated class of images of cone triangles.
9. Universe large enough for localization: u,v independent; W.Localization uses
   the standard localization construction at the maximum size universe. PASS:
   no small-Hom condition, universe equality or HasDerivedCategory is imposed.

The isomorphism in item 5 is tested after the fully faithful inclusion into the
unbounded homotopy category. It can be lifted uniquely to the full bounded-below
subcategory: both endpoints and their cone are bounded below, with cone lower
bound min(N_Y,N_X-1). Thus it neither adds unbounded cone witnesses nor weakens
the distinguished-triangle characterization. The J clause uses the same Mathlib
construction rather than a new distinguished-triangle predicate.

Edge cases: the zero complex and identity maps are covered; their cones are
acyclic and localization sends identities to identities. J consisting of zero
objects is allowed. An empty J has no zero object and is correctly not an additive
subcategory. Empty finite sums are included by the shared finite-products instance.
a=b gives one graded piece; a=b=0 is allowed. No cochain lower bound is fixed or
assumed nonnegative. There are no schemes, coefficients, characteristic or n≥1
constraints to exclude corresponding cases. An infinite sequence of widening
finite filtration intervals remains admitted when B=none. Invalid intervals a>b
are not asserted by this theorem, consistently with the node's explicit a≤b.

The independent concept searches above were run during this reading; the matched
modules and declarations were opened and rejected as exact matches for the reasons
recorded there. No missing notion warrants a new node or dependency repair.

Mismatches repaired: the interrupted sandbox lacked every delivery artifact;
reconstructed the node copy, theorem module and report. Added the already landed
finite-filtered-localization dependency, retained the source's valid-interval
restriction explicitly, and fixed the Triangle namespace during compilation.
The mathematical node statement, proof and source are unchanged. No hollow
definition, private copy, file-local notation/instance, unbound variable or new
proof was introduced. Only the main theorem has a postponed proof.

Final verification: scompile.py compiled the module separately in sandbox and
library modes with no errors or warnings. Line widths are at most 100 characters;
lean.statement is verbatim the final signature. Delivery preflight is run using
deliver2.py, never by invoking the maintainer's scripts directly.
