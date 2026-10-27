## Worker report

The module `Sheaf.CategoryTheory.DerivedCategory.LeftAcyclicShortExact` states
`CategoryTheory.leftAcyclic_shortExact`, with its only proof `sorry`. There are no
new definitions, extra nodes, dependency repairs, or statement corrections. The node
copy changes only `lean`. Q27's 2026-10-22 PASS is the stage-1 split review, not a
stage-2 Lean binding: the assigned node still has no `lean` record. This delivery
formalizes that reviewed split without resplitting or changing it.

Hypothesis-by-hypothesis correspondence:

- The two abelian categories are `(A : Type uA) (B : Type uB)`, with separate
  `[Category.{vA} A]`, `[Category.{vB} B]`, `[Abelian A]`, and `[Abelian B]`.
- Enough projectives is `[EnoughProjectives A]`. I read Mathlib's
  `Projective`, `ProjectivePresentation`, and `EnoughProjectives`: these assert
  precisely lifting against every epi and a projective epimorphism onto every object.
- The additive, right exact functor is `(V : A ⥤ B) [V.Additive]
  [PreservesFiniteColimits V]`. Between abelian categories this is precisely
  preservation of cokernels and finite direct sums; no left exactness is assumed.
- The chosen derived categories and localization sizes are
  `[HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]`. All six object,
  morphism, and localization universes are declared and independent. `DerivedCategory.Q`
  localizes cochain complexes; `DerivedCategory.Qh` is the canonically factored
  homotopy-category localization. The node explicitly permits these equivalent models.
- The functor is `(LV : DerivedCategory A ⥤ DerivedCategory B)`. Its canonical
  natural comparison is
  `ε : DerivedCategory.Q ⋙ LV ⟶ V.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
  DerivedCategory.Q`. The binder `hLV : LV.IsLeftDerivedFunctor ε
  (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))` fixes its universal
  right Kan extension property. Thus `ε` cannot be an arbitrary natural map.
- Everywhere-definedness in the stronger Stacks 05S9 sense is `hdefined`: for
  EVERY unbounded homotopy-category object `X`, there is a value `Y` making
  `MorphismProperty.Over.forget (HomotopyCategory.quasiIso A (.up ℤ)) ⊤ X ⋙
  Over.forget X ⋙ V.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh`
  an `IsEssentiallyConstantProDiagram` with value `Y`. This is the body of the
  recorded `Functor.IsTriangulatedLeftDerivedDefinedAt`, expanded at the fixed
  quasi-isomorphism system. It uses the recorded predicate and diagram, without
  redefining them or adding saturation/exactness as hypotheses. The same expanded
  interface is already used in the landed
  `CategoryTheory.boundedAbove_acyclic_leftDerived_computation`, which I read.
- The arbitrary short exact sequence is `(S : ShortComplex A) (hS : S.ShortExact)`.
  By the read Mathlib definitions this means `S.f ≫ S.g = 0`, exactness, a monic
  first arrow and an epic second arrow. Set `M' = S.X₁`, `M = S.X₂`, `M'' = S.X₃`,
  `i = S.f`, and `p = S.g`.

Clause-by-clause correspondence:

- Left acyclicity of each `S.Xᵢ` is written directly as
  `IsIso (ε.app ((CochainComplex.singleFunctor A 0).obj S.Xᵢ))`.
  Applying `V` termwise to a single complex gives the single complex of `V(S.Xᵢ)`
  through the canonical single-functor comparison. Invertibility is unchanged by
  that canonical identification. No weaker cohomology-only criterion replaces it.
- The first conjunct assumes acyclicity of `S.X₁` and `S.X₃`, then concludes
  acyclicity of `S.X₂` AND `(S.map V).ShortExact`: exactly clause (1).
- The second conjunct assumes acyclicity of `S.X₂` and `S.X₃`, then concludes
  acyclicity of `S.X₁` AND `(S.map V).ShortExact`: exactly clause (2).
- `ShortComplex.map` has objects `V.obj S.Xᵢ` and arrows `V.map S.f`, `V.map S.g`.
  Its `ShortExact` conclusion is therefore the SAME specified image sequence in
  both clauses, including injectivity of the first arrow and surjectivity of the last.

Dependency declarations read and used:

- `def-sp-abelian`: `CategoryTheory.Abelian`,
  `Mathlib.CategoryTheory.Abelian.Basic`, re-exported by the derived-category import.
- `def-weil-abstract-derived-category`: `DerivedCategory`, `HasDerivedCategory`,
  `DerivedCategory.Q`, `DerivedCategory.Qh`,
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`.
- `def-pur-saturated-triangulated-localization`:
  `CategoryTheory.Functor.IsTriangulatedLeftDerivedValue` and
  `CategoryTheory.Functor.IsTriangulatedLeftDerivedDefinedAt`, in
  `WeilConjectures.CategoryTheory.IsSaturatedTriangulatedMultiplicativeSystem`.
  I read both complete signatures and their bodies. Their diagram condition uses
  `CategoryTheory.IsEssentiallyConstantProDiagram`, whose complete definition and
  docstring in `WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro`
  were also read. The full expanded defining condition appears as `hdefined`.
- Proof-only imports include the recorded Mathlib homotopy triangulation and cone
  declarations (`HomotopyCategory.instIsTriangulatedIntUp`,
  `HomotopyCategory.Pretriangulated.distinguishedTriangles`,
  `HomotopyCategory.mappingCone_triangleh_distinguished`),
  `HomotopyCategory.quasiIso_saturated_triangulated` in
  `WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated`,
  `CategoryTheory.ShortComplex.ShortExact.singleTriangle_distinguished` in
  `Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle`,
  `CategoryTheory.Functor.leftDerived_exact_when_defined` in
  `WeilConjectures.CategoryTheory.LeftDerivedExactWhenDefined`, and
  `DerivedCategory.HomologySequence.exact₁`, `exact₂`, `exact₃` in
  `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`. These source signatures
  and the available docstrings were read. The node's proof-only dependency
  `lem-trf-left-derived-object-cohomology` currently has no recorded declaration or
  Mathlib match; it is named in the proof docstring, with its source-based proof role,
  and has no import yet. It is not required to type the present statement.

Source and edge cases:

I read `literature/stacks-project/derived.tex` at Situation 05S8, Definition 05S9,
Lemma 015C (`lemma-F-acyclic`), and Lemma 015D (`lemma-F-acyclic-ses`) with its proof.
The two clauses are the opposite-category duals of 015D(1) and (2). The existing
node deliberately assumes the unbounded everywhere-defined total functor and enough
projectives, and those assumptions are retained. The proof docstring reproduces all
six split steps, including identifying the degree-zero arrows by counit naturality.

The all-zero sequence is allowed. With the identity or zero functor every object is
acyclic and the conclusions reduce to the expected short exact sequence. Split short
exact sequences are covered without any splitting hypothesis. For tensoring abelian
groups with Z/2, the sequence Z → Z → Z/2 with first map multiplication by 2 does not
contradict either clause: the quotient Z/2 is not left acyclic. In the kernel argument,
`q = -1` uses `q - 1 = -2`, and both are negative; no degree-zero vanishing is silently
assumed. No object, morphism, or chosen-localization universes are equated, no complexes
are restricted to be bounded, and no exactness or triangulatedness of `LV` is added.
No node fault or `STATEMENT-DISPUTED` issue was found.

Searches before writing (2026-10-22):

- `msearch.py ... leanfinder "Left acyclic objects for an additive right exact functor
  are closed under extensions and kernels of epimorphisms"`: eight hits, including
  `Functor.exact_tfae`, finite-colimit criteria, and closure of inverse-image object
  properties for exact functors; none is the total-counit acyclicity theorem.
- `msearch.py ... leansearch "Acyclic objects for a right exact additive functor are
  closed under extensions and kernels of epimorphisms"`: eight hits, including
  `ObjectProperty.IsClosedUnderExtensions.mk`, right exact functors and ordinary
  complex acyclicity; no exact statement match.
- `msearch.py ... loogle '"leftDerived"'`: abstract `IsLeftDerivedFunctor` and
  `HasLeftDerivedFunctor`/`totalLeftDerived` interfaces; no acyclic short-exact theorem.
- `msearch.py ... grep 'acyclic|leftDerived|ShortExact' CategoryTheory/Abelian`:
  short-exact functor preservation and the classical individual derived-functor
  interface; no total-counit closure result. I also read
  `Mathlib.CategoryTheory.Functor.Derived.LeftDerived`, especially the universal
  property class used in the signature.
- `rg` over both `lean/WeilConjectures` and `lean/Sheaf` for
  `IsTriangulatedLeftDerivedDefinedAt|IsTriangulatedLeftDerivedValue|left.*[Aa]cyclic|Left.*Acyclic`
  and for `acyclic.*shortExact|acyclic.*short_exact|leftAcyclic|left_acyclic|acyclic_leftDerived`
  found the bounded-above acyclic-computation consumer and the generic derived-value
  interfaces, but no declaration of this theorem or separate acyclicity definition.
  Searching the item id found only the bounded-above consumer's proof docstring.

Validation: `scompile.py N8 lem-trf-left-acyclic-short-exact` compiled the sandbox and
the actual library module separately, both cleanly (1.3 s and 1.4 s). All variables
and universes are explicitly bound, and `autoImplicit` is explicitly disabled.

## Second reading by N8

The dispatcher brief reserves independent review to the maintainer and prohibits
starting another agent. This section records the submitting worker's final reread,
not an independent worker review. With the node and file open, I checked that the
first implication uses X₁/X₃ and concludes X₂, the second uses X₂/X₃ and concludes X₁,
and both conclude short exactness for the actual `S.map V`. I also checked retention
of enough projectives, right exactness, the universal comparison, and the all-object
essential-constancy condition. No correction was needed after that reread.
