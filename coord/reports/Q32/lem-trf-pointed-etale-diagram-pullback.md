## Worker report

The module `Sheaf.AlgebraicGeometry.PointedEtaleDiagramPullback` states
`AlgebraicGeometry.exists_pointed_etale_diagram_pullback`, with `sorry` as its sole
proof. No definitions, additional nodes, dependency repairs, or statement corrections
are needed.

Source read: `literature/stacks-project/curves.tex`, Tag 0CBY,
`lemma-etale-local-structure-nodal-family`, statement and the first paragraph of the
first proof (lines 5077–5121). This explicitly pulls the finite-type diagram back to
the original base. The node expands this operation and the marked-point retention.
The statement-dependency declarations and their docstrings were read directly in
the Mathlib files named below.

Hypothesis correspondence:

- The schemes are the ten explicit `Scheme.{u}` binders. `f0 : X0 ⟶ S0` and
  `y : Y ⟶ T` are the initial morphisms.
- `p0`, `e0`, and their `Etale` instances give the two etale charts. `w0` and `τ0`
  are the specified morphisms. `m0 : U0 ⟶ pullback y τ0`, its `Etale` instance,
  and `hm0` give exactly the etale V0-morphism into the model.
- `hw0 : w0 ≫ e0 = p0 ≫ f0` is the initial commutative square.
- `u0 : U0` is the specified point; x0 is written directly as `p0 u0`.
- `f : X ⟶ S` is arbitrary. The open subschemes are represented by `X'`, `S'`
  with `iX : X' ⟶ X`, `iS : S' ⟶ S` and their `IsOpenImmersion` instances.
  An open immersion identifies its source with its open image, so this is exactly
  a presentation of the two open subschemes, allowing all of them. The restriction
  is `f' : X' ⟶ S'` with `hf' : f' ≫ iS = iX ≫ f`. This both expresses
  f(X') ⊆ S' and determines the restricted morphism uniquely, since iS is mono;
  it imposes no extra condition beyond the node's image containment.
- `c : S' ⟶ S0`, `α : X' ≅ pullback f0 c`, and `hα` give the specified
  isomorphism over S'. In the statement write q = α.hom ≫ pullback.fst f0 c.
  `x : X'` and `hx : q x = p0 u0` give the specified lift of x0.

Conclusion correspondence (the following names are explanations, not extra Lean
definitions or arbitrary data): put V = pullback e0 c, U = pullback p0 q,
P = pullback (p0 ≫ f0) c, Z0 = pullback y τ0, and
Z = pullback y (pullback.fst e0 c ≫ τ0).

- The first two conjuncts assert etaleness of e = pullback.snd e0 c ≫ iS and
  p = pullback.snd p0 q ≫ iX, exactly the projections followed by inclusions.
- `β : U ≅ P` is the first asserted canonical isomorphism. Its two projection
  identities specify the map `(a,b)` from proof step 1, where a is U → U0 and
  b is U → X' → S'. These identities determine β uniquely by pullback.hom_ext.
- `γ : P ≅ pullback w0 (pullback.fst e0 c)` is the second asserted canonical
  isomorphism. Its U0 and S' projection identities determine it uniquely: the
  V0 projection of its V component is already forced by the defining pullback
  relation. Thus these are canonical identifications, not unspecified isomorphisms.
- The equation `w = β.hom ≫ γ.hom ≫ pullback.snd ...` defines the induced w.
  The structure morphism τ is written explicitly as pullback.fst e0 c ≫ τ0.
- `m : U ⟶ Z`, `Etale m`, and the equation for m's second projection give the
  etale V-morphism. Its first-projection equation fixes its Y component to the
  original m0's Y component, pulled back along a.
- The displayed equation beginning `w ≫ pullback.snd e0 c ≫ iS` is e ∘ w = f ∘ p.
- The two projection equations for `r : Z ⟶ Z0` fix the canonical comparison map.
  `IsPullback a m m0 r` expresses precisely that m is the base change of m0,
  including commutativity of that specified square. Together with the projection
  characterizations of β and γ this is the claimed base change under the canonical
  identifications. It adds no additional mathematical condition.
- The existential `z : ↥U` has a(z) = u0 and t(z) = x. Its third equation gives
  p(z) = iX(x), the node's final point assertion interpreted in X.
- The final universal quantifier is over every element of Γ(T, O_T), written
  `T.presheaf.obj (Opposite.op ⊤)`. Its equality is
  pr_V0.appTop (τ0.appTop a) = (pr_V0 ≫ τ0).appTop a, exactly h = τ* a.

Dependency declarations used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`, and
  `Scheme.Hom.appTop`, in `Mathlib.AlgebraicGeometry.Scheme` (source lines
  36–77, 175–185); these supply schemes, morphisms, and pullback of functions.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback`, `.fst`, `.snd`,
  `.lift`, in `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`
  (source lines 94–133). The existing scheme pullback instance is used.
- `def-weil-etale-morphism`: `AlgebraicGeometry.Etale`,
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`, source lines 38–45.
- `def-weil-open-immersion`: `AlgebraicGeometry.IsOpenImmersion`,
  `Mathlib.AlgebraicGeometry.OpenImmersion`, source lines 35–39.

The public Etale import exposes these statement dependencies, including the
pullback-square predicate `CategoryTheory.IsPullback`. The plain proof import
`Mathlib.AlgebraicGeometry.PullbackCarrier` supplies
`Scheme.image_preimage_eq_of_isPullback` for `lem-weil-pbc-base-change-image`
(source lines 420–430). The Etale import also supplies the recorded proof
interfaces `Etale.etale_isStableUnderBaseChange`, `Etale.etale_comp`, and the
open-immersion etale instance for `lem-weil-pbc-etale-scheme-base-change` and
`lem-weil-pbc-etale-composition-cancellation` (source lines 69–90, 130–137).
No distinct Sheaf dependency modules exist or are necessary for these Mathlib leaves.
The docstring reproduces all six proof steps, naming the DAG facts used.

Edge cases checked: empty opens and schemes are allowed; a supplied u0 or x
makes the corresponding empty-point case impossible without adding nonemptiness
hypotheses. Identity base change and whole-scheme open immersions are included.
No reducedness, finite type, Noetherian, characteristic, rational-point, or
residue-field-equality hypothesis is imposed. Compatible underlying points do lift
to a point of the scheme fibre product (not necessarily uniquely), as expressed
by `Scheme.Pullback.exists_preimage_pullback`, read at lines 300–308. The theorem
therefore asserts only existence of z. A single explicit universe u is used for
schemes, with no equality imposed between unrelated site/coefficient universes.
All term and universe variables are explicit; autoImplicit is disabled for the theorem.

Searches made for the entire statement:

- msearch.py / leanfinder: "Pull back a pointed etale chart diagram of schemes
  through arbitrary base change and open restrictions retaining its model map and
  marked point" returned eight hits, including scheme etale pullbacks and
  Pullback.Triplet.ofPoint; none states the complete diagram assertion.
- msearch.py / loogle: "CategoryTheory.Limits.pullback, AlgebraicGeometry.Etale"
  returned Etale.instFstScheme, Etale.instSndScheme, and
  exists_etale_isCompl_of_quasiFiniteAt. These cover projections or a different
  existence statement, not the full node.
- msearch.py / grep: "pullbackAssoc|pullbackRightPullbackFstIso|exists_preimage_pullback"
  in AlgebraicGeometry returned 25 hits for individual identifications and point
  lifting. None assembles this statement.
- rg in both lean/WeilConjectures and lean/Sheaf, with
  "pointed.*[Ee]tale|pointedEtale|pointed_etale|lem-trf-pointed-etale-diagram-pullback",
  found other pointed-neighbourhood material and the parent NodalEtaleChart, but
  no declaration for the full item. An exact search for the proposed declaration,
  module name, and item id found no match. The upstream name index was also searched.
- The required exact grep of the item id in lean/WeilConjectures found no match.

Validation: scompile.py compiled both the sandbox statement and its intended library
module cleanly. An initial elaboration error in the existential point binder was
repaired by making the scheme-to-point-type coercion explicit (`↥(pullback ...)`).
The delivered file contains no diagnostic commands. No mathematical node fault
or disputed statement was found.

## Second reading by Q32

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
