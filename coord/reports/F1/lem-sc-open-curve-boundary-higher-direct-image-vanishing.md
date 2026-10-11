## Worker report

The module `Sheaf.AlgebraicGeometry.Curve.OpenCurveBoundaryHigherDirectImageVanishing`
states `AlgebraicGeometry.isZero_gm_higherDirectImage_stalk_of_open_curve_boundary`.
Its only proof is `sorry`; no definitions, extra nodes or dependency modules are needed.
The item's statement and dependencies are unchanged.

Hypothesis and conclusion correspondence:

- Algebraically closed field k: `{k : Type u} [Field k] [IsAlgClosed k]`.
- Proper smooth connected curve Cbar over k: `Cbar : Scheme.{u}`, its structure
  morphism `f : Cbar ⟶ Spec (.of k)`, and `[IsConnectedCurve f] [Smooth f] [IsProper f]`.
  The recorded `IsConnectedCurve` extends `IsCurve`: separation, finite type,
  connectedness, nonemptiness and dimension exactly one are all included.
  The explicit structure morphism is used because the recorded curve class takes it.
- Finite set S of closed points: `(S : Set Cbar) (hS : S.Finite)` and
  `(hclosed : ∀ P ∈ S, IsClosed ({P} : Set Cbar))`.
- C = Cbar minus S and j its inclusion: `C : Scheme.{u}`, `(j : C ⟶ Cbar)` with
  `[IsOpenImmersion j]` and `(hj : Set.range j.base = Sᶜ)`.
  An open immersion identifies its domain, with its scheme structure, with the
  open subscheme on its image. Thus these binders express exactly the complement
  inclusion up to the canonical isomorphism; C is not an arbitrary source of a map.
- Every geometric point: `{Ω : Type u} [Field Ω] [IsSepClosed Ω]` and
  `(xbar : Spec (.of Ω) ⟶ Cbar)`, the recorded small-etale-point convention.
- Exactly degrees 1 and 2: `(q : ℕ) (hq : q = 1 ∨ q = 2)`.
- The etale sheaf of units on C: `C.gmSheaf`, an existing abelian sheaf whose
  values are the additively written, universe-lifted units of global sections.
- Place this sheaf in degree zero using `DerivedCategory.Plus.singleFunctor ... 0`;
  apply `Etale.rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} j` and then
  `DerivedCategory.Plus.homologyFunctor ... (q : ℤ)` to obtain R^q j_* G_m.
- Its geometric stalk is `((Scheme.pointSmallEtale xbar).sheafFiber
  (A := AddCommGrpCat.{u + 1})).obj ...`.
- Vanishing is `IsZero` of this object of AddCommGrpCat, meaning the trivial
  abelian group. This is not `IsZero` on a bare type.

Dependency declarations read and used:

- def-sc-curves: `WeilConjectures.AlgebraicGeometry.Curve`,
  `AlgebraicGeometry.IsCurve` and `AlgebraicGeometry.IsConnectedCurve`.
- def-weil-pbc-direct-image: `AlgebraicGeometry.Etale.lowerStar` in
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`;
  `AlgebraicGeometry.Etale.rightDerivedLowerStarPlus` is actually declared in
  `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence`, imported here.
  Its body is the bounded-below right derived functor of that same lowerStar.
- def-sc-gm-torsor: `AlgebraicGeometry.Scheme.gmSheaf` is declared in
  `WeilConjectures.AlgebraicGeometry.Sites.Gm`, imported here. The recorded
  `CategoryTheory.Sheaf.Torsor` in `WeilConjectures.CategoryTheory.Sites.Torsor`
  was also read; the present statement uses only the units sheaf, not torsors.
- def-weil-open-immersion: `AlgebraicGeometry.IsOpenImmersion` in
  `Mathlib.AlgebraicGeometry.OpenImmersion` (available transitively).
- def-weil-pbc-geometric-stalks: `CategoryTheory.GrothendieckTopology.Point.sheafFiber`
  in `Mathlib.CategoryTheory.Sites.Point.Basic`, and
  `AlgebraicGeometry.Scheme.pointSmallEtale` in `Mathlib.AlgebraicGeometry.Sites.EtalePoint`.
- def-weil-pbc-etale-cohomology: read `AlgebraicGeometry.Etale.cohomology` and
  `AlgebraicGeometry.Etale.rightDerivedGlobalSections` in
  `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`. They define field-level
  cohomology used in the natural-language proof. The conclusion involves cohomology
  sheaves of derived direct image, not global sections, so no unused import of
  LowerShriek was added.

Sources: the local literature checkout is absent on this machine. Read the authoritative
online [Tag 03RJ](https://stacks.math.columbia.edu/tag/03RJ) and
[Tag 03RM](https://stacks.math.columbia.edu/tag/03RM). The node explicitly adapts the
former's strict-henselization calculation to an open curve. At interior points the
immersion is locally the identity; at boundary points the fibre is the fraction field
of a strictly henselian DVR, algebraic over the curve function field. Hilbert 90 and
Brauer vanishing give precisely the requested degrees. The declaration docstring
records all three steps and their DAG references.

Edge cases checked: S may be empty (j is then an isomorphism, and positive higher
images vanish); a boundary consisting of one or several closed points is allowed.
The generic point cannot belong to S, so the open complement is nonempty. The curve
cannot be empty or zero-dimensional because IsConnectedCurve requires dimension one
and connectedness. Points of the interior and of the boundary are both quantified.
Degree zero is deliberately excluded: j_* G_m generally has nontrivial stalks.
No characteristic restriction, affine-source hypothesis, or rationality assumption
on geometric points is added. All variables and the universe are explicitly bound;
coefficients are AddCommGrpCat in u+1, matching the recorded six-functor convention.

Searches for an existing statement:

- `msearch.py ... leanfinder`: query "stalks of first and second higher direct images
  of the multiplicative group along an open immersion of a smooth curve vanish".
  Eight hits: scheme stalk injectivity and module restriction-stalk comparisons,
  and an unrelated smooth sheaf stalk; no matching etale G_m vanishing statement.
- `msearch.py ... loogle`: query `AlgebraicGeometry.IsOpenImmersion,
  CategoryTheory.Limits.IsZero`; zero hits.
- `msearch.py ... grep`: query `higherDirect.*[Gg]m|[Gg]m.*higherDirect|jstar.*[Gg]m`;
  zero Mathlib hits.
- `msearch.py ... leansearch`: query "higher direct image multiplicative group open
  immersion smooth curve geometric stalk vanishes"; service unavailable:
  Internal Server Error. No mathematical verdict is inferred from that failure.
- `rg` of the source repository, `lean/Sheaf`, and `dag/lean_names_upstream.json` for
  `higherDirect.*[Gg]m|[Gg]m.*higherDirect|jstar.*[Gg]m` and the proposed declaration:
  no hits. Search by this item's id in the source repository also returned no hits.
  Broader searches for gmSheaf and higher direct images found the reusable notions
  above and general higher-direct-image lemmas, not this statement.
- Read the upstream `WeilConjectures.AlgebraicGeometry.Curve.Brauer` module:
  its vanishing statements concern global H^2, not geometric stalks of R^q j_*.

Validation: the server single-file compile succeeded in 2.3 seconds with no errors
or warnings. Delivery dry run is the final mechanical check; the independent second
reader will supply its own section and deliver.

## Second reading by F1

I independently opened the item JSON, its delivered module, all six statement-dependency
nodes, and the source declarations below. The correspondence list is:

- Object and hypothesis k algebraically closed: `{k : Type u} [Field k]
  [IsAlgClosed k]`. Exact.
- Proper smooth connected curve Cbar over k: `{Cbar : Scheme.{u}}`,
  `(f : Cbar ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] [IsProper f]`.
  Exact. Read `Curve.lean`'s classes: IsConnectedCurve extends IsCurve, which gives
  separation, locally finite type, quasi-compactness and dimension at most one;
  the connected class adds ConnectedSpace and dimension exactly one. No additional
  Noetherian, integral, affine, or projective hypothesis is imposed.
- Finite set S of closed points: `(S : Set Cbar) (hS : S.Finite)` and
  `(hclosed : ∀ P ∈ S, IsClosed ({P} : Set Cbar))`. Exact; closedness is singleton
  closedness, not just closedness of the union.
- C is the open complement and j its inclusion: `{C : Scheme.{u}}`,
  `(j : C ⟶ Cbar) [IsOpenImmersion j] (hj : Set.range j.base = Sᶜ)`.
  Exact up to the canonical scheme isomorphism: the Mathlib open-immersion definition
  includes the structure-sheaf isomorphism, so this cannot be an arbitrary morphism
  with the right set-theoretic image. No extra structure map on C is needed.
- Every geometric point of Cbar: `{Ω : Type u} [Field Ω] [IsAlgClosed Ω]
  (xbar : Spec (.of Ω) ⟶ Cbar)`. Exact after repair. Opening
  `def-weil-pbc-geometric-stalks`, then `def-weil-pbc-scheme-conventions` and its
  `def-weil-geometric-point` pointer, revealed that the project's geometric-point
  notion requires algebraically closed Ω. The worker used `[IsSepClosed Ω]`,
  which also quantified over additional fields, strengthening the statement.
  Changed this binder to `[IsAlgClosed Ω]` in the module and its recorded signature.
  Mathlib pointSmallEtale still applies, since algebraically closed fields are
  separably closed. This repairs the Lean to the unchanged node; no node correction.
- Both requested degrees: `(q : ℕ) (hq : q = 1 ∨ q = 2)` follows the point binder.
  Exact: the universally quantified theorem gives both q=1 and q=2, and does not
  assert any other degree.
- Coefficient sheaf G_m on C: `C.gmSheaf`. Exact. Opened `Sites/Gm.lean`:
  etaleStructurePresheaf evaluates global sections of each etale scheme;
  gmPresheaf applies unitsAddCommGrpULift, and gmSheaf bundles this as a sheaf.
  This is the existing declaration explicitly listed by def-sc-gm-torsor.
- Higher direct image R^q j_* G_m:
  `(DerivedCategory.Plus.singleFunctor (Sheaf C.smallEtaleTopology
  AddCommGrpCat.{u + 1}) 0).obj C.gmSheaf`, then
  `(Etale.rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} j).obj`, then
  `(DerivedCategory.Plus.homologyFunctor (Sheaf Cbar.smallEtaleTopology
  AddCommGrpCat.{u + 1}) (q : ℤ)).obj`. Exact. Opened the recorded
  UpperLowerStar/Defs declaration lowerStar, which is sheaf pushforward along
  etale base change; Derived/UpperLowerStarCoherence derives that functor on D+.
  Mathlib DerivedCategory/Plus defines singleFunctor as the degree-q single complex
  and homologyFunctor by restriction of unbounded derived cohomology.
- Conclusion: `IsZero (((Scheme.pointSmallEtale xbar).sheafFiber
  (A := AddCommGrpCat.{u + 1})).obj ...)`. Exact. Opened EtalePoint.lean's
  pointSmallEtale (fiber consists of lifts over xbar) and Point/Basic.lean's
  presheafFiber/sheafFiber (colimit over opposite pointed neighborhoods).
  The result is an abelian group object, so IsZero means a trivial stalk.

The remaining recorded dependency, Etale.cohomology/rightDerivedGlobalSections in
Derived/LowerShriek, was also opened: it computes derived global sections and then
cohomology. It occurs in the node's proof, not in the conclusion; adding an unused
import is unnecessary. The torsor structure in Sites/Torsor was read as well; no
torsor object is needed here. No new nodes or dependency modules are in this delivery,
and none are needed: the recorded declarations give all notions used.

Source reading: the local Stacks checkout is absent. Independently read the Stacks
etale-cohomology.tex from
https://raw.githubusercontent.com/stacks/stacks-project/master/etale-cohomology.tex,
including section-higher-Gm's standing hypotheses and lemma-higher-direct-jstar-Gm
(Tag 03RJ), and the discussion through theorem-vanishing-cohomology-Gm-curve
(Tag 03RM). That section fixes an algebraically closed base field and a smooth
curve; its j denotes the generic-point inclusion. The node explicitly adapts the
strict-henselization calculation to the open complement, so I did not mistake the
source's generic-point j for this node's j. Boundary stalks use the same fraction
field calculation; interior stalks vanish by local identity. The delivered docstring
carries all three node proof steps, including the Noetherian qc/qs reduction,
strict-henselization stalk formula, DVR/injectivity/generic-point identification,
algebraic fraction-field extension, Hilbert 90 and degree-two Brauer vanishing.

Edge cases: S=empty is allowed, and then the immersion is an isomorphism. Singleton
and larger finite boundaries are allowed without enumerations or a Nonempty S
instance. Every point is quantified, including interior and generic points and
boundary closed points. Cbar cannot be empty or zero-dimensional by the node's
connected-curve definition; finite closed points cannot remove its generic point,
so no empty-complement case is silently excluded. q=0 is correctly excluded, since
j_*G_m need not vanish. All characteristics are allowed; no invertibility or
prime-to-characteristic hypothesis appears. Zero means zero in AddCommGrpCat,
not IsZero on a bare Type. The common universe u is polymorphic and matches the
recorded geometric-point and Scheme encodings; the units sheaf uses the required
ULift into AddCommGrpCat.{u+1}. All variables and universes are explicitly bound.

Independent searches (recorded by msearch in searches.jsonl):

- LeanFinder: "higher pushforward of units sheaf on punctured regular curve has
  trivial geometric fibers in degrees one and two". Eight unrelated hits (scheme
  function fields, germs, and bottom-open sections); no matching statement.
- Loogle: `AlgebraicGeometry.Scheme.gmSheaf`. Service returned unknown identifier;
  no mathematical verdict from that query.
- LeanSearch: "first second derived pushforward units sheaf open complement closed
  points smooth curve stalk trivial". Service returned Internal Server Error;
  explicitly unavailable, not a no-match claim.
- msearch grep: `gmSheaf|multiplicative.*group|higherDirectImage_stalk`.
  The Mathlib hits were algebraic multiplicative groups, not this vanishing.
- Independent rg over Mathlib/AlgebraicGeometry, upstream WeilConjectures and
  repository lean/Sheaf for `isZero.*gm|gm.*isZero|R.?[12].*j|higher.*[Uu]nits|
  [Uu]nits.*higher|higherDirectImage_stalk` found no matching declaration.
  Broader rg of the upstream curve files for gmSheaf/rightDerivedLowerStar/higher
  direct images found Brauer.lean's global degree-two cohomology and
  DivisorSequence.lean's ordinary direct-image exact sequence. Opened their relevant
  statements: neither states vanishing of these geometric stalks. Existing notions
  are reused, and no existing statement replaces this module.

H5/H6/H8/H9: no definitions are introduced, the only theorem proof remains `sorry`,
all imports serve notions in the signature, source/blueprint docstrings are present,
there is no local notation/private copy/hidden let binder, and lines meet the width
convention. Only mismatch found and repaired: IsSepClosed Ω versus IsAlgClosed Ω.
The earlier Worker report describes the original binder and is retained as requested;
this independent reading supersedes that assertion. The node statement, dependencies,
proof and all other correct Lean were left unchanged. Its lean.statement was updated
verbatim to the repaired signature.

Validation: repaired module compiled cleanly via scompile.py in 1.9 seconds,
exit code 0, no warnings. Exact signature equality and Lean line widths checked.
