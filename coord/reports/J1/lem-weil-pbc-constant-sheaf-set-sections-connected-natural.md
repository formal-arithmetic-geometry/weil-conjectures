## Worker report

Module: `Sheaf.AlgebraicGeometry.ConstantSheafSetSectionsConnectedNatural`.
Declaration: `AlgebraicGeometry.Scheme.constantSheaf_set_sections_connected_natural`.
It states the bijection from a set to the global sections of its constant small-etale
sheaf on a nonempty connected scheme, together with compatibility under every morphism
of schemes over the algebraically closed base field. Its only proof is `sorry`; it
introduces no definitions, axioms, or instances.

Hypothesis and clause correspondence:

- The algebraically closed field is `(Ω : Type u) [Field Ω] [IsAlgClosed Ω]`.
- The scheme over that field is `(U : Scheme.{u}) [U.Over (Spec (.of Ω))]`.
- Nonempty and connected is `[ConnectedSpace U]`. The recorded dependency explicitly
  includes nonemptiness as `ConnectedSpace.toNonempty`; no redundant nonempty binder is
  needed. The empty scheme is excluded exactly as in the node.
- The arbitrary set is `(E : Type u)`. There is no finiteness, inhabitedness, algebraic
  structure, or decidable equality assumption. `ULift.{u + 1, u} E` places its unchanged
  elements in the value universe for sheafification on the small etale category;
  `u` is explicitly bound and arbitrary, as in the representability dependency.
- The constant sheaf is `(constantSheaf U.smallEtaleTopology (Type (u + 1))).obj
  (ULift.{u + 1, u} E)`, named by the local let `F`. Mathlib defines this to be the
  sheafification of the constant presheaf. The first conclusion uses the same
  sheafification directly through `toSheafify`; these codomains are definitionally
  identical, not separately defined constant sheaves.
- Evaluation at `(Opposite.op (Etale.mk (𝟙 U)))` means sections over the terminal
  object `U → U`. The function inside `Function.Bijective` sends `e` to the
  sheafification-unit image of `⟨e⟩`. Thus the assertion is about the canonical map
  itself, rather than an unspecified bijection.
- Every scheme `V` over Ω, every morphism `v : V ⟶ U`, and its being over Ω are
  the universal binders `(V : Scheme.{u}) [V.Over (Spec (.of Ω))] (v : V ⟶ U)
  [v.IsOver (Spec (.of Ω))]` in the second conjunct. No `Etale v`, connectedness,
  nonemptiness, finite type, or other condition on `V` is imposed.
- `b := MorphismProperty.Over.pullback @Etale ⊤ v` is base change on the small etale
  sites. `etaleSetPullback v` is the existing sheafification-after-left-Kan-extension
  construction for sheaves of sets. The local `adj` is its existing Mathlib
  adjunction to direct image, and `(adj.unit.app F).hom.app ...` is precisely
  the section pullback `v*` specified in the node's proof.
- The canonical identification with the constant sheaf on `V` is rendered by
  `∃ γ : (etaleSetPullback v).obj F ≅ G` together with the displayed equation
  for every `e : E`. The left side applies `γ` to the unit-pullback of `η_U(e)`;
  the right side is `η_V(e)`, evaluated on `b.obj (Etale.mk (𝟙 U))`.
  This object is `U ×_U V`, a terminal object canonically isomorphic to `V`.
  Transporting both sides along that isomorphism gives exactly the node's equation
  on global sections over `V`. It avoids assuming a non-etale `V → U` is an object
  or a restriction morphism in `U.Etale`.
  The iso is specified by these equations on constants: constants generate `F`
  locally, restrictions come from the terminal object, and the pullback adjunction
  therefore makes this the canonical comparison iso. No arbitrary choice of an
  unrelated identification is used in the equation.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`, including `toNonempty`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Scheme.Etale`, `Etale.mk`, `Etale.forget`.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology`.
- `Mathlib.CategoryTheory.Sites.Sheaf`: `CategoryTheory.Sheaf` and its underlying presheaf.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`;
  its definition is `Functor.const ⋙ presheafToSheaf`.
- `Mathlib.CategoryTheory.Sites.Sheafification`: `CategoryTheory.toSheafify`.
- `Sheaf.AlgebraicGeometry.ConstantSheafSetsRepresentable`:
  `Scheme.constantSetCoproductPresheaf` and `Scheme.constantSheaf_sets_representable`.
  The full signature and docstring were read. This supplies the representation used
  by the node's first proof step, and imports the constant-sheaf/sheafification
  infrastructure used in the statement.
- `Sheaf.AlgebraicGeometry.EtaleSheaves`: `Scheme.etaleSetPullback` (full definition and
  docstring read). Its already-landed node `def-weil-pbc-etale-sheaves` is added to
  `stmt_deps` so this established notion is cited rather than redefined.
- `Mathlib.CategoryTheory.Sites.Pullback`:
  `Functor.sheafPullbackConstruction.sheafAdjunctionContinuous` (full construction
  read). For continuity-instance inference its topology arguments use
  `smallGrothendieckTopology @Etale`, the definition of `smallEtaleTopology`.

Edge cases checked: `E` empty has no global sections on nonempty `U`, and its naturality
formula is vacuous. A singleton set gives exactly one section. An empty `U` would
invalidate the bijection for a general `E`, and is correctly excluded. Empty or
disconnected `V` are included; pulling a constant gives the same value on every
component (and the unique section on the empty scheme). Arbitrary, including infinite,
sets are allowed. No condition on field characteristic occurs. Identity morphisms
and non-etale morphisms are covered by the same adjunction unit formula.

Searches for an existing statement (2026-10-11):

- `msearch.py leansearch`, query `constant sheaf of sets global sections connected scheme`:
  service unavailable, Internal Server Error; no result obtained.
- `msearch.py leanfinder`, query `global sections of set valued constant etale sheaf on
  connected scheme natural under pullback`: eight hits for structure-sheaf constants,
  Scheme Γ, and module sections; none for this set-valued assertion.
- `msearch.py loogle`, query `CategoryTheory.constantSheaf, Function.Bijective`: zero hits.
- `msearch.py grep`, query `constantSheaf|ConnectedSpace`, subdirectory
  `AlgebraicGeometry/Sites`: only the continuous-map-presheaf file and its import;
  neither states this theorem.
- `rg` in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for
  `constant.*(sections|bijective)|connected.*constant`: the closest is
  `Scheme.bijective_toSheafify_app_terminal` in
  `AlgebraicGeometry/Sites/ConstantSheafSections.lean`, whose full signature has
  `M : AddCommGrpCat.{u + 1}`. It is abelian-group-valued, not arbitrary sets.
  The full `Etale.constantSheafIsoContinuousMapSheaf` declaration in the upstream
  constant-sheaf file likewise assumes `AddCommGroup A`; it is not a match.
- `rg` of this item's id in the source repository: no match.
- `rg` of constant-sheaf/connected-section terminology in `lean/Sheaf`: the existing
  representability module, etale-set pullback, and unrelated module-valued sections;
  no identical statement.
- `rg` of the proposed declaration name in Mathlib, upstream, `lean/Sheaf`, and
  `dag/lean_names_upstream.json`: no name clash.

Source checked directly at https://stacks.math.columbia.edu/tag/03P5 (the local
literature checkout is absent): sections are Zariski-locally-constant functions;
its representability argument does not use the group law. Tag 093R was also opened
for the inverse-image compatibility referenced by the node's proof. No node
statement correction or dispute is needed.

Validation: the final module compiled cleanly on the server with `scompile.py`,
with no errors or warnings. The required delivery dry run is run after this record.


## Second reading by J1

Independent second reading on 2026-10-11. I opened the sandbox node and module,
every statement-dependency node, the recorded Mathlib declarations, and the full
ConstantSheafSetsRepresentable and EtaleSheaves dependency modules. Verdict:
the Lean says exactly what the node says. No mathematical or Lean repair is needed;
this reading adds only the independent review record.

Object, hypothesis and conclusion checklist:

- Algebraically closed base field Omega: `(Ω : Type u) [Field Ω] [IsAlgClosed Ω]`.
  Exact, with arbitrary characteristic.
- Scheme U: `(U : Scheme.{u})`, Mathlib's locally affine locally ringed space.
  Its structure over Omega is `[U.Over (Spec (.of Ω))]`. Exact; no finite type,
  separatedness, Noetherian or other geometric hypothesis is added.
- Nonempty connected U: `[ConnectedSpace U]`. I read its Mathlib declaration:
  it extends PreconnectedSpace and contains `toNonempty : Nonempty U`.
  This is exactly def-weil-connected-scheme, including exclusion of empty U.
- Arbitrary set E: `(E : Type u)`, without any structure or finiteness hypothesis.
  `ULift.{u + 1, u} E` is a universe lift, bijective with E, not a restriction
  to groups. The arbitrary universe u is the existing representability and
  set-pullback convention: any set and schemes can be placed in a common larger
  universe. No bounded cardinality or finite-set assumption occurs.
- Small etale site and set-valued sheaf: `U.smallEtaleTopology` on `U.Etale`,
  using the recorded Mathlib declarations. I checked the jointly-surjective-cover
  criterion and the full-subcategory definition of `Sheaf`.
- Constant sheaf and canonical constant sections: `constantSheaf` is definitionally
  constant presheaf followed by `presheafToSheaf`; `toSheafify` is its unit.
  Both occurrences use the same lifted value set. Evaluation at
  `Opposite.op (Etale.mk (𝟙 U))` evaluates at the terminal etale U-scheme.
- Bijection of the canonical map: `Function.Bijective (fun e : E => ... ⟨e⟩)`
  asserts precisely injectivity and surjectivity of that unit map, rather than
  existence of an unspecified bijection. Exact.
- Every Omega-morphism v from V: the second conjunct universally binds
  `(V : Scheme.{u}) [V.Over (Spec (.of Ω))] (v : V ⟶ U)` and
  `[v.IsOver (Spec (.of Ω))]`. It adds no connectedness or etaleness of V or v.
- Inverse image and section pullback: `b` is base change on the small etale sites;
  `etaleSetPullback v` is the recorded existing left-Kan-extension/sheafification
  functor. I read its definition and Mathlib's
  `sheafPullbackConstruction.sheafAdjunctionContinuous`: `adj` uses precisely that
  constructed left adjoint. Its unit evaluated at the terminal object pulls a
  global section to the object `b.obj (Etale.mk (𝟙 U))` of V's site.
- Same constant value under the canonical identification: the existential sheaf
  iso gamma and its equation for every e identify the pulled-back constant
  section with `toSheafify` applied to the same e on V. The base-changed object
  is U times_U V, canonically terminal, hence evaluation there is canonically
  global sections on V. The equation suffices to specify the canonical comparison:
  by bijectivity, it specifies the adjoint map on every section of F at U;
  naturality specifies its action on constant sections at every etale U-object,
  and these generate F locally by sheafification. The adjunction and the
  sheafification universal property then give uniqueness of the sheaf morphism.
  Thus the existential iso does not leave an arbitrary identification of values.

Source reading: the local literature checkout is absent. I fetched the original
Stacks `etale-cohomology.tex` and `sites-modules.tex` into the sandbox scratchpad
and read `remark-constant-locally-constant-maps` (03P5), its sites section,
and `lemma-pullback-locally-constant` (093R). The first identifies sections with
Zariski locally constant functions via the disjoint union; its group law is not
used in this argument, giving the node's set-valued form. The site section starts
with an arbitrary scheme S; it imposes no hidden finiteness or Noetherian assumption.
The second covers inverse images under morphisms of topoi, including sets.
The representability dependency gives precisely the set-valued disjoint union,
canonical unit factorization and unique isomorphism used in proof step 1.
The existing set-pullback definition is the needed notion, not the upstream
abelian-category-only inverse-image functor. No new nodes or dependency modules
are present; no statement correction is present or necessary.

Edge cases: empty E gives empty global sections on nonempty U and a vacuous
naturality equation; singleton E gives one section. Empty U is intentionally
excluded, since for arbitrary E its unique section would destroy the bijection.
Empty and disconnected V are allowed, as are non-etale v and identity v; the
same constant value occurs on every component, and the empty V has its unique
section. Infinite sets and all characteristics are covered. There is no integer
index n, zero object or additive structure in this statement. Universes and all
variables are explicitly bound; I verified the node's signature equals the
module signature verbatim.

Independent searches, with queries different from the first reader's:

- LeanFinder via msearch: `bijection between a set and sections of its constant
  sheaf on a connected etale site`. Eight hits: generic global-section equivalences
  and constant-sheaf predicates; no connected-scheme set-valued bijection/naturality.
- Loogle via msearch: `"constantSheaf", "Bijective"`. Zero hits.
- LeanSearch via msearch: `constant sheaf of arbitrary sets connected scheme
  canonical section pullback`. Service unavailable (Internal Server Error),
  recorded without claiming a negative search result.
- Independent rg for `constant.*(terminal|sections)`, `bijective_toSheafify`,
  and `constantSheaf.*[Ii]so` in upstream Sites and project's AlgebraicGeometry
  modules, plus inspection of Mathlib ConstantSheaf/Pullback. The closest upstream
  `Scheme.bijective_toSheafify_app_terminal` binds `M : AddCommGrpCat.{u + 1}`;
  I opened its full declaration and surrounding variables. It excludes arbitrary
  sets, particularly the empty set, and does not state the second conjunct.
  Other hits concern module sections or geometric stalks, not this statement.
- Full-name rg across Mathlib, upstream, project Lean and upstream name index:
  no collision with `constantSheaf_set_sections_connected_natural`.

H5-H9: there are no definitions, hollow data, or auxiliary proved statements;
the sole proof is `sorry`. Source/blueprint docstrings are present, and the theorem
explains the three proof steps with their dependency ids. Both imports serve the
statement/proof: representability imports the constant-sheaf infrastructure and
supplies step 1; EtaleSheaves supplies the set inverse-image functor. No line
exceeds 100 characters. The server scompile check succeeded cleanly (2.1 seconds),
without warnings or errors. An initial compile invocation used a relative path
from the read-only repository and failed to locate the sandbox file; repeating
with the absolute sandbox path succeeded. No file change was needed.
