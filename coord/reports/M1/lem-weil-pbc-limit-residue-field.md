## Worker report

The module `Sheaf.AlgebraicGeometry.LimitResidueField` states
`AlgebraicGeometry.exists_isColimit_residueField_of_isLimit`, with a `sorry` proof.
It states both the ring colimit and scheme limit claims of Stacks Tag 0CUG (1).
Source checked directly at https://stacks.math.columbia.edu/tag/0CUG because the
local literature/stacks-project/limits.tex is not present on this machine.
The source agrees with the node. No statement correction, new nodes, or dependency
modules are needed. No STATEMENT-DISPUTED issue was found.

Hypotheses and clauses, in order:

- Directed set: `{I : Type w} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]`.
  The explicit nonempty instance is part of Stacks' definition of directed set,
  not an additional mathematical assumption. Preorders permit equivalent indices.
- Inverse system of schemes: `D : Iᵒᵖ ⥤ Scheme.{u}`. Its functor laws give the
  identity and composite identities for the transition maps.
- Affine transitions: `[∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]`.
- The given limit S with its projections: `c : Cone D`, `hc : IsLimit c`;
  S is `c.pt` and f_i is `c.π.app (op i)`.
- The point s: `s : c.pt`. Its image s_i is literally `c.π.app (op i) s`.
- The induced directed system of fields is existentially packaged as a functor
  `R : I ⥤ CommRingCat.{u}`. The object equalities fix its rings to exactly
  `(D.obj (op i)).residueField (c.π.app (op i) s)`. The map condition
  `HEq (R.map f) ((D.map f.op).residueFieldMap (c.π.app (op j) s))` fixes
  every transition to the induced field map. This is NOT an unconstrained system:
  HEq is equality with transport of the dependent source/target types. The
  point equality needed for those types is the cone identity evaluated at s.
  This avoids introducing a second definition of a residue-field diagram or
  writing internal functoriality proofs in a definition during stage 2.
- The induced cocone is `r : Cocone R`, with `r.pt = c.pt.residueField s` and
  `HEq (r.ι.app i) ((c.π.app (op i)).residueFieldMap s)` for each i. Thus
  the ring and all coprojections are the canonical ones. `Nonempty (IsColimit r)`
  is precisely their universal property in commutative rings, not in fields.
- The equivalent scheme assertion uses `t : Cone (R.op ⋙ Scheme.Spec)`, fixes
  `t.pt = Spec (c.pt.residueField s)`, and fixes each projection by HEq to
  `Spec.map ((c.π.app (op i)).residueFieldMap s)`. `Nonempty (IsLimit t)`
  gives the universal property in the category of all schemes.
- The scheme transition maps are affine: the last quantified clause inside
  the existential for t is `IsAffineHom ((R.op ⋙ Scheme.Spec).map f)`.
- Compatibility with the canonical maps into S and S_i is explicitly the first
  final conjunction: `Spec.map (f_i.residueFieldMap s) ≫ j_s_i = j_s ≫ f_i`.
- Compatibility for every transition is the second final conjunction:
  `Spec.map (f_ji.residueFieldMap s_j) ≫ j_(f_ji(s_j)) = j_s_j ≫ f_ji`.
  Here `f_ji(s_j) = s_i` by the cone law. Mathlib's canonical point map at
  that equal point is used directly, avoiding an unrecorded choice of cast.
  These two clauses say exactly that the canonical maps form a morphism of
  inverse systems and that the induced map of limits is j_s.

Dependency declarations read and used:

- def-pc-scheme: `AlgebraicGeometry.Scheme` and `Scheme.Hom`,
  Mathlib.AlgebraicGeometry.Scheme (scheme structure and morphisms).
- pqf-def-affine-morphism: `AlgebraicGeometry.IsAffineHom`,
  Mathlib.AlgebraicGeometry.Morphisms.Affine (affine-open preimage condition).
- lem-weil-pbc-limit-affine-transition:
  `AlgebraicGeometry.exists_limit_affine_transition`,
  Sheaf.AlgebraicGeometry.LimitAffineTransition, imported. Its full signature
  and proof docstring were read. This item's hypothesis already supplies a
  limiting cone; there is no reason to choose a new limit via the existence
  theorem. The imported module provides the inverse-system affine context.
- def-weil-residue-field: `Scheme.residueField`, `Scheme.Hom.residueFieldMap`,
  Mathlib.AlgebraicGeometry.ResidueField. Read their definitions and docstrings,
  the identity/composition lemmas, `Scheme.residueFieldCongr`, and
  `Scheme.fromSpecResidueField` and its naturality lemma. These are the actual
  quotient residue fields, induced local-ring maps, and canonical point maps.
- def-weil-pbc-category-colimit: `CategoryTheory.Limits.Cocone`, `IsColimit`,
  `colimit`, `colimit.desc` (Mathlib.CategoryTheory.Limits.HasLimits and its
  imported Cones/IsLimit modules). We use the universal property rather than
  choosing a colimit object unrelated to the fixed field κ(s).
- def-weil-affine-spectrum: `AlgebraicGeometry.Spec`, `Spec.map`,
  `Scheme.Spec`, Mathlib.AlgebraicGeometry.Scheme. Read definitions and signatures.

Edge cases checked before writing:

- Empty directed indices are excluded by the source's definition (Nonempty I).
- Empty limit schemes have no s, so there is no assertion to make in that case.
- Singleton indices and constant systems give the field itself and its identity
  cocone; all map identifications and both naturality clauses reduce correctly.
- Zero rings may occur among affine coordinate rings. A point supplies a prime
  and thus a genuine residue field; no nonzero-ring assumption has been added.
- No reducedness, integrality, quasi-compactness, quasi-separatedness, or
  characteristic assumption is imposed on the original schemes.
- The index universe w is independent of the scheme universe u. No universe
  constraint excludes large index sets relative to the schemes. The field
  diagram lies in CommRingCat.{u}, as the actual residue fields do.
- The test rings and schemes in IsColimit/IsLimit are all objects of the same
  ring/scheme categories as the system; this is the standard universe-relative
  universal property, with no restriction to fields or affine test schemes.

Searches for an existing statement and for name collisions:

- msearch.py leanfinder: "residue field of a point of an inverse limit of
  schemes is the directed colimit of residue fields". Eight hits, including
  Scheme.residue_descResidueField, its reassociated version, Scheme.over_def,
  Scheme.residue_residueFieldMap, Scheme.fromSpecResidueField_apply and
  Scheme.SpecMap_residue_apply; these concern residue maps and naturality,
  not the colimit statement.
- msearch.py loogle: "AlgebraicGeometry.Scheme.residueField,
  CategoryTheory.Limits.IsColimit". Zero hits.
- msearch.py grep: "residueField.*(colimit|IsLimit)|colimit.*residueField",
  AlgebraicGeometry. Zero hits.
- msearch.py leansearch: "residue field of inverse limit of schemes with
  affine transition maps is colimit of residue fields". Service unavailable:
  Internal Server Error. Recorded as unavailable, with no negative verdict.
- rg over WeilConjectures and lean/Sheaf for the same colimit patterns and
  the item id: no matching statement or blueprint declaration. The node's
  earlier three-kind searches likewise found no matching statement.
- rg over Mathlib, WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json
  for exists_isColimit_residueField_of_isLimit: no existing declaration.

Validation: scompile.py M1 lem-weil-pbc-limit-residue-field compiled the module
on the server in 1.8 seconds, exit code 0, with no errors or warnings.
All variables and universes are explicitly bound. The only proof is `by sorry`.

## Second reading by M1

Read the sandbox node and module independently against Stacks limits.tex,
label lemma-inverse-limit-irreducibles, part (1), including the surrounding
section and the proof. The local TeX is absent; read the upstream TeX at
https://raw.githubusercontent.com/stacks/stacks-project/master/limits.tex
and the rendered tag https://stacks.math.columbia.edu/tag/0CUG.
The subsequent situation-descent introduces quasi-compactness and
quasi-separatedness AFTER this lemma; neither is a standing assumption here.
Definition 00D3 explicitly uses a nonempty directed preorder, not necessarily
an antisymmetric order.

Object, hypothesis and conclusion checklist (each verdict: exact):

1. Directed set I: `{I : Type w} [Preorder I]
   [IsDirected I (· ≤ ·)] [Nonempty I]`. These give precisely reflexivity,
   transitivity, common upper bounds and nonemptiness from 00D3.
2. Schemes S_i with inverse transition maps and their laws:
   `D : Iᵒᵖ ⥤ Scheme.{u}`. For `f : i ⟶ j`, `D.map f.op`
   goes from S_j to S_i, matching the node's direction.
3. Affine transitions: the instance binder quantifies over every arrow of
   Iᵒᵖ and asserts `IsAffineHom (D.map f)`; no assumption on the stages
   being affine or on the projections is added.
4. Limit S and projections f_i: `c : Cone D`, `hc : IsLimit c`;
   S is `c.pt`, f_i is `c.π.app (op i)`. This takes any given limit,
   as the node does, rather than choosing another limit.
5. Point s and its images s_i: `(s : c.pt)` and the literal expression
   `c.π.app (op i) s` throughout. No arbitrary family of points is assumed.
6. Directed residue-field system: `∃ (R : I ⥤ CommRingCat.{u})`, with
   every object equal to `(D.obj (op i)).residueField (c.π.app (op i) s)`
   and every map HEq to `(D.map f.op).residueFieldMap (c.π.app (op j) s)`.
   Cone naturality identifies the image of s_j with s_i. Transport along
   this point equality supplies the indicated heterogeneous equality;
   proof irrelevance makes the choice of equality proof immaterial.
   Thus the quantified diagram cannot choose other ring maps.
7. Canonical cocone on κ(s): `r : Cocone R`, `r.pt = c.pt.residueField s`,
   and `HEq (r.ι.app i) ((c.π.app (op i)).residueFieldMap s)` for every i.
   These fix both the ring and all maps. `Nonempty (IsColimit r)` is the
   universal property against every commutative ring, including the zero
   ring, and not merely against fields.
8. Scheme-limit form: `∃ t : Cone (R.op ⋙ Scheme.Spec)`, with vertex equal
   to `Spec (c.pt.residueField s)` and all projections HEq to the spectra
   of the canonical residue maps; `Nonempty (IsLimit t)` is the limit in
   all schemes, not just affine schemes. R's map constraints also fix
   the transition maps of this inverse system.
9. Affine spectrum transitions: the final universally quantified clause
   inside the existential for t is `IsAffineHom ((R.op ⋙ Scheme.Spec).map f)`.
   It is the node's parenthetical clause, and follows for maps of spectra.
10. Compatibility of projections with canonical point maps: the first
    final conjunction is `Spec.map (f_i.residueFieldMap s) ≫ j_s_i = j_s ≫ f_i`.
11. Compatibility on transitions: the second final conjunction is
    `Spec.map (f_ji.residueFieldMap s_j) ≫ j_(f_ji(s_j)) = j_s_j ≫ f_ji`.
    The point in the first canonical point map equals s_i by c's cone law.
    Together these clauses say the canonical point maps are a morphism
    of systems whose map on limits is j_s. No clause is missing.

Dependency signatures opened: Scheme and Scheme.Hom in Scheme.lean;
IsAffineHom in Morphisms/Affine.lean; residueField, Hom.residueFieldMap,
residueFieldMap_id, residueFieldMap_comp, fromSpecResidueField and its
naturality in ResidueField.lean; Spec, Spec.map and Scheme.Spec in
Scheme.lean; Cocone in Limits/Cones.lean and IsColimit in Limits/IsLimit.lean.
The residue field is the quotient of the actual stalk by its maximal ideal,
and its maps are induced by the local stalk maps. These are exactly the
notions recorded by the dependency nodes. Also opened the full signature
and docstring of exists_limit_affine_transition in LimitAffineTransition.lean:
its context agrees with the node; the present statement supplies its own
limiting cone, so it need not invoke that existence theorem or inherit its
single-universe binder. No dependency module or new definition node is needed.
No statement_change is present and no correction is needed.

Edge cases: the empty index is excluded by 00D3 itself; a singleton index
and a constant identity system reduce to the ordinary residue field and
its identity maps. Empty limit schemes have no point s. Empty stages
likewise cannot admit a projected s. Zero coordinate rings are allowed,
but a point supplies a nonzero residue field without an extra hypothesis.
No characteristic, integrality, reducedness, finiteness, separation or
Noetherian hypothesis occurs. There is no n parameter. Universes u and w
are explicitly bound and independent; the field rings and spectra live
in the same universe as the original schemes, and the universal properties
quantify over their entire respective categories.

Independent searches using different wording from the worker:

- msearch.py leanfinder: "residue fields commute with affine transition
  inverse limits of schemes". Eight hits, consisting of canonical-point
  naturality, residue-field congruence, descent and pullback identities.
  Opened the relevant naturality declaration; it supplies only the final
  compatibility clauses, not the colimit or limit universal property.
- msearch.py loogle: "AlgebraicGeometry.Scheme.residueField,
  CategoryTheory.Limits.Cocone". Zero hits.
- msearch.py leansearch: "The residue fields of compatible points in an
  inverse system with affine transition maps have colimit the residue field
  at the limit point". Internal Server Error; service unavailable, so no
  negative verdict is inferred.
- rg (case insensitive) for residue-field/limit in either order over
  Mathlib/AlgebraicGeometry, WeilConjectures and lean/Sheaf found only
  unrelated henselization, henselian-colimit and fibre-base-change uses
  in the project, and no matching theorem. The exact proposed name and
  blueprint id are absent from WeilConjectures, lean/Sheaf and the upstream
  name registry. No existing declaration replaces this module.

No mathematical or formal mismatch found, and no Lean or node text changed.
The declaration docstring carries all seven proof steps with their node
citations. There are no definitions (hollow or otherwise), private notions,
extra theorems or proved results; the only proof is the required `by sorry`.
All variables and universes are bound. The recorded lean.statement is
verbatim the file's signature. Server compilation and delivery dry-run
results are recorded below.

Validation completed: scompile.py compiled the unchanged module in 1.8 seconds,
exit code 0, without warnings. A literal signature comparison succeeded and
all Lean lines meet the 100-character bound. deliver2.py --no-push printed
OK: preflight and compilation passed (dry-run commit c3582d086).

## Reviewer fix (R-lrf1143)

Index universe: `{I : Type w}` with an independent `universe w` replaced by `{I : Type u}` (the schemes' universe, STATE line INDEX UNIVERSES FOR LIMITS AND FILTERED COLIMITS; C1 02bc80ff3, G1 117cfd333, M1 d2371fc68). The report's claims that w is independent of u are superseded. No other change; recompiled clean.
