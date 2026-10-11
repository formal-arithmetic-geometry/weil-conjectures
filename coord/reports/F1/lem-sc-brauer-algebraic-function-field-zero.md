## Worker report

The module `lean/Sheaf/AlgebraicGeometry/Curve/BrauerAlgebraicExtension.lean` states
`AlgebraicGeometry.IsConnectedCurve.isZero_etaleCohomology_gm_algebraic_extension`.
The only proof is `sorry`; no definitions, dependency modules, new nodes, or statement
corrections are needed.

Hypothesis and conclusion correspondence:

- Algebraically closed field k: `(k : Type u) [Field k] [IsAlgClosed k]`.
- C/k: `(C : Scheme.{u}) [C.Over (Spec (.of k))]`; the structure morphism is
  `C ↘ Spec (.of k)`.
- Integral: `[IsIntegral C]`.
- Connected curve: `[IsConnectedCurve (C ↘ Spec (.of k))]`, the recorded source's
  class extending `IsCurve` (separated, locally finite type, quasi-compact,
  dimension at most one) with `ConnectedSpace C` and dimension exactly one.
  Thus the nonempty, connected and one-dimensional clauses are all present.
- Function field: `C.functionField`, Mathlib's generic stalk, with its canonical
  field instance for integral C. This is the integral clause explicitly endorsed
  by def-sc-function-field's record and module, not the general component product.
- Algebraic extension L/k(C): `(L : Type v) [Field L] [Algebra C.functionField L]
  [Algebra.IsAlgebraic C.functionField L]`. The algebra map is the field embedding.
- Finite-dimensional separable field extension E/L: `(E : Type w) [Field E]
  [Algebra L E] [FiniteDimensional L E] [Algebra.IsSeparable L E]`.
  Algebra.IsSeparable means every minimal polynomial is separable (and implies
  algebraicity); FiniteDimensional means finite as an L-vector space.
- Spec(E) with its small etale site: `Spec (.of E)` and
  `(Spec (.of E)).smallEtaleTopology`.
- G_m: `(Spec (.of E)).gmSheaf`, the recorded sheaf of units of the structure
  sheaf, written additively and universe-lifted to AddCommGrpCat.{w + 1}.
- H^2 with the node's cohomology: `(Etale.cohomology AddCommGrpCat.{w + 1}
  (Spec (.of E)) 2).obj` applied to G_m placed in degree zero by
  `DerivedCategory.singleFunctor ... 0`. This uses the recorded total-right-derived
  global sections definition directly, not the Ext-based Sheaf.H carrier.
- Zero group: `CategoryTheory.Limits.IsZero` of that AddCommGrpCat object, exactly
  triviality of its underlying abelian group. It is not IsZero of a bare Type.

Dependency declarations read and used:

- def-sc-curves: `WeilConjectures.AlgebraicGeometry.Curve`,
  `AlgebraicGeometry.IsCurve` and `AlgebraicGeometry.IsConnectedCurve` (full class
  fields and docstrings read).
- def-sc-function-field: `Sheaf.AlgebraicGeometry.FunctionField`,
  `Scheme.functionFieldOfComponents`; its integral clause explicitly reuses
  `Mathlib.AlgebraicGeometry.FunctionField`, `Scheme.functionField`, used here.
  The unused component-product module is not imported.
- def-pc-field-extension: `Mathlib.Algebra.Algebra.Defs`, `Algebra`.
- def-weil-pbc-separable-algebraic-extension: the mathlib_match
  `Mathlib.FieldTheory.Separable`, `Algebra.IsSeparable` (including its
  algebraicity instance).
- def-weil-pbc-etale-cohomology:
  `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`,
  `AlgebraicGeometry.Etale.cohomology` and `rightDerivedGlobalSections`.
- def-weil-pbc-etale-sheaves: `CategoryTheory.Sheaf` in
  `Mathlib.CategoryTheory.Sites.Sheaf`, specialized to
  `Sheaf X.smallEtaleTopology AddCommGrpCat.{w + 1}` as the node's mixed record
  prescribes. The module `Sheaf.AlgebraicGeometry.EtaleSheaves` was read; its
  unrelated set-valued predicates are not imported or duplicated.
- def-sc-gm-torsor: `WeilConjectures.CategoryTheory.Sites.Torsor`,
  `CategoryTheory.Sheaf.Torsor`, read but not required in this statement;
  the recorded second declaration `AlgebraicGeometry.Scheme.gmSheaf` in
  `WeilConjectures.AlgebraicGeometry.Sites.Gm` is used.

Additional Mathlib signatures read: `Algebra.IsAlgebraic` in
RingTheory/Algebraic/Defs and `FiniteDimensional` in LinearAlgebra/FiniteDimensional/Defs.
All universes are explicitly declared. L and E have independent universes v and w;
no restriction to finite L/k(C), no separability of L/k(C), no smoothness or
properness of C, and no chosen algebra structure on E over k(C) are imposed.
The latter can be induced by composing the given embeddings when proving the result.

Edge cases checked before writing: C cannot be empty or a point because connected
curves have dimension one; singular integral curves and nonproper curves are allowed.
The trivial extensions L=k(C) and E=L are allowed, as are infinite algebraic L
and inseparable L/k(C) in positive characteristic. E/L need not be Galois.
There is no characteristic restriction. The zero ring is excluded only because
L and E are fields, as the node requires. IsZero in AddCommGrpCat means the group
has only its zero element. The theorem agrees with the C1 argument in all these cases.

Searches for an existing statement (msearch.py queries recorded in searches.jsonl):

- leansearch: "second etale cohomology Gm algebraic extension of curve function
  field vanishes": service unavailable, Internal Server Error.
- leanfinder: "The second etale cohomology of Gm vanishes over a finite separable
  extension of an algebraic extension of a curve function field": eight unrelated
  hits (Hilbert 90 H1, cotangent H1 and finite-field function-field class numbers).
- loogle: "Algebra.IsAlgebraic, Algebra.IsSeparable, Subsingleton": zero hits.
- grep: "Brauer|brauer|CohomologicalBrauer" in Mathlib AlgebraicGeometry:
  zero hits. Direct rg in WeilConjectures and lean/Sheaf finds the original
  function-field vanishing in Curve/Brauer and the C1-field theorem in
  Sites/BrauerGroup, neither with the extension hypotheses of this node.
- Direct rg for this node id in WeilConjectures: no declaration.
- Direct rg for the proposed declaration name in dag/lean_names_upstream.json:
  no collision.

Source verification: the local literature checkout is absent; the blueprint source
was read in full over ssh from the server at the recorded path. Its third proof
paragraph descends a central simple algebra to a finite subextension of k(C) and
uses Tsen. The node's reviewed C1 reformulation has the same conclusion and is
included step by step in the theorem docstring with all three proof dependencies.
No node fault or statement dispute was found.

Validation: scompile.py on the project server compiled the module cleanly in
2.8 seconds, exit code 0, no warnings. The delivery dry run is the final gate.

## Second reading by F1

I independently read the sandbox node and BrauerAlgebraicExtension.lean, all seven
statement-dependency nodes, and the declarations underlying the notions used here.
The source is the blueprint, not a Stacks lemma: I read the complete
sec-curve-estimates/sk-prop-h2/lem-sc-function-field-cd-one.md over SSH from the
server's literature checkout. Its statement introduces algebraically closed k,
an integral connected curve C/k and algebraic L/k(C); its first proof paragraph
introduces finite separable E/L, and its third paragraph proves Br(E)=0 by finite
coefficient descent and Tsen. No extra smoothness, properness, characteristic-zero,
or Galois hypothesis is assumed there.

Object, hypothesis and conclusion checklist (each verdict: exact):

- k is an algebraically closed field: `(k : Type u) [Field k] [IsAlgClosed k]`.
- C is a scheme over k: `(C : Scheme.{u}) [C.Over (Spec (.of k))]`, with its
  structure morphism `C ↘ Spec (.of k)`; the Over convention supplies the chosen map.
- C is a connected curve: `[IsConnectedCurve (C ↘ Spec (.of k))]`. I read
  IsCurve and IsConnectedCurve in WeilConjectures.AlgebraicGeometry.Curve: the
  latter extends the former, so separatedness, local finite type, quasi-compactness
  (together finite type), dimension at most one, connectedness/nonemptiness and
  dimension exactly one are present. These match def-sc-curves, without smoothness.
- C is integral: `[IsIntegral C]`; this supplies the irreducible-space and field
  structures needed by its generic stalk, without a stronger hypothesis.
- k(C) is the function field: `C.functionField`. I read Mathlib's definition as
  `C.presheaf.stalk (genericPoint C)` and the component-product module recorded by
  def-sc-function-field. That module explicitly directs the integral clause to
  this existing generic stalk; importing the unused component product is unnecessary.
- L is a field extension of k(C): `(L : Type v) [Field L]
  [Algebra C.functionField L]`. I read Algebra's ring-map and scalar compatibility
  fields; for fields the ring map is injective, as def-pc-field-extension requires.
- L/k(C) is algebraic: `[Algebra.IsAlgebraic C.functionField L]`. Mathlib's class
  requires every element to satisfy a nonzero polynomial, with no finite-degree or
  separability condition on L.
- E is a field extension of L: `(E : Type w) [Field E] [Algebra L E]`.
- E/L is finite-dimensional: `[FiniteDimensional L E]`, Mathlib's Module.Finite
  abbreviation for the vector space furnished by that same Algebra instance.
- E/L is separable: `[Algebra.IsSeparable L E]`. I read its signature and its
  isAlgebraic instance in Mathlib.FieldTheory.Separable; every minimal polynomial
  is separable. This is the dependency's separable algebraic extension notion.
- The base of cohomology is Spec(E) with its small etale site:
  `(Spec (.of E)).smallEtaleTopology`; no curve cohomology is substituted.
- The coefficient sheaf is G_m: `(Spec (.of E)).gmSheaf`. I read gmSheaf,
  gmPresheaf and etaleStructurePresheaf in Sites.Gm: its sections are the units
  of Gamma(U,O_U), written additively and lifted, exactly def-sc-gm-torsor's sheaf.
- The abelian sheaf category is `Sheaf (Spec (.of E)).smallEtaleTopology
  AddCommGrpCat.{w + 1}`. I read Mathlib's Sheaf full-subcategory definition and
  the mixed def-weil-pbc-etale-sheaves record; its unrelated new set-valued
  predicates are not needed. The existing abelian-sheaf clause is used directly.
- The group is H^2 of this sheaf: `Etale.cohomology ... 2` applied to
  `DerivedCategory.singleFunctor ... 0` on gmSheaf. I read cohomology and
  rightDerivedGlobalSections in LowerShriek: these are R(Gamma) followed by
  degree-2 homology. Thus this is the recorded cohomology definition, with G_m
  in degree zero, rather than the distinct Ext-based Sheaf.H carrier.
- The sole conclusion is that this group is zero: `IsZero` of the resulting
  AddCommGrpCat object. This says the abelian group is trivial; it is not IsZero
  of an uncategorified Type. Quantifiers run k, C, L, E, in the node's order.

Edge cases: empty schemes and zero-dimensional points are excluded by the node's
connected-curve definition itself (dimension exactly one), not by a new condition.
Integral singular curves and nonproper curves remain allowed. The trivial extensions
L=k(C), E=L, arbitrary infinite algebraic L, and inseparable L/k(C) in positive
characteristic are allowed; E/L is required separable but need not be Galois.
Fields already exclude the zero ring. No index family or variable n is present;
the cohomology degree is exactly 2. Universes u, v, w are explicitly bound and
L and E have independent universes; C and k share the standard Scheme-over-field
universe, with larger presentations available by lifting. There is no universal
quantification over test algebras in a smaller universe and no extra scalar-tower
instance imposed: the composite embedding k(C) -> E can be constructed in the proof.

Independent searches, with different queries from the first worker:

- LeanSearch via msearch.py: `Tsen algebraic extension function field second
  cohomology multiplicative group zero`; service unavailable (Internal Server Error).
  This is recorded as unavailable, not as evidence of absence.
- LeanFinder via msearch.py: `Tsen theorem Brauer vanishing for algebraic field
  extensions`; eight hits concerning BrauerGroup, CSA, centrality, finite dimension
  and formal etaleness, none stating this result.
- Loogle via msearch.py: `Algebra.IsAlgebraic, IsZero` reported an unknown identifier;
  retry `Algebra.IsAlgebraic, CategoryTheory.Limits.IsZero` returned zero hits.
- rg for `brauer|tsen|etaleCohomology_gm` throughout lean/Sheaf and
  WeilConjectures; read the nearby signatures in Curve/Brauer and Sites/BrauerGroup.
  The former vanishes only for the original function field; the latter assumes
  IsQuasiAlgClosed on its input field. Neither introduces this L/E extension tower
  or has this theorem's statement. Mathlib Algebra/BrauerGroup contains definitions
  of CSA and Brauer equivalence, not this vanishing assertion.
- rg for the item id and proposed declaration name in WeilConjectures and
  dag/lean_names_upstream.json found no collision. No duplicate definition is added.

No mismatch was found, and no Lean or node text was changed. There are no new
nodes, dependency modules, hollow definitions, or statement corrections to review.
The only theorem proof is sorry. Both docstrings name the blueprint source and item;
the theorem docstring follows all three DAG proof steps: algebraicity and finite
coefficient subextension, Tsen plus finite-extension C1 stability, then C1 Brauer
vanishing. The recorded lean.statement is verbatim equal to the file signature.
All binders and universes are explicit, all imports provide used notions, and no
Lean line exceeds 100 characters. Independent scompile.py validation passed in
2.0 seconds, exit code 0, with no warnings. The second reading changes only this
report by adding the independent review.
