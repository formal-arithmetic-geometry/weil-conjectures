1. Files written:

- `dag/nodes/sec-picard-framework/lem-pc-rf-mv-triangle-naturality.json` (repaired statement split).
- `dag/nodes/sec-picard-framework/lem-pc-derived-mayer-vietoris-functorial.json` (statement-only dependency; no Mathlib match).
- `dag/nodes/sec-picard-framework/def-pc-derived-base-change-map.json` (definition dependency; no Mathlib match).
- `citations.json` (verbatim proof-step citations).

2. Attachments: none.

3. WANTED: none.

4. The returned split failed because it asserted the connecting-map square from the first two squares and treated the canonical base-change map as merely named. I added a statement-only functoriality node covering the degreewise K-injective short exact sequences, the connecting morphism, and compatibility with affine direct image. I also added a definition node for the canonical derived base-change morphism and cited both in Step 2. Step 1 now explicitly derives qcqs and quasi-compactness of the primed cover from affine S and S' (Tags 01KU and 01S5).

5. Nothing remains unfinished.

## Review by G1

I read the target node, unit `sk-thm-picard-semicon`, chapter record, parent Tag 0DJ9 context, and the existing relative Mayer--Vietoris node. I reread `lem-pc-derived-mayer-vietoris-triangle` and `lem-pc-derived-direct-image-composition`. For the new functoriality node I checked the 08BV construction: both triangles come from degreewise short exact sequences of K-injective complexes, and a map of such sequences induces a morphism of triangles including the connecting map; the affine direct-image compatibility is the same construction after applying the affine direct image. For the new base-change definition I checked the 07A7/0736 adjunction construction and stated its restriction to each open W.

Step 1 uses the MV and composition nodes and now checks the affine hypotheses needed on X' and the primed opens. Step 2 uses the base-change definition for the first two squares and the new functoriality node for the connecting-map square; it also checks compatibility of affine Rg'_* with the primed MV triangle and shift preservation. The step is non-elementary. Every cited statement is quoted verbatim in `citations.json`.

I ran the required Mathlib searches for the item: LeanFinder returned only generic Mayer--Vietoris/sheaf and homology naturality declarations, Loogle returned no hit, grep found only generic `triangleOfSES` declarations and no scheme base-change naturality, LeanSearch was unavailable, and the AlgebraicGeometry grep found no derived base-change triangle result. The node's blueprint ancestor and exact proof clause were checked with `blueprint_refs.py`; `same_as` is empty. No statement or source error was found.

## Second reading by G1

## Not duplicates

def-pc-derived-base-change-map vs lem-weil-pbc-exact-functor-derived-functor: the new node defines the canonical base-change morphism; the existing node concerns exactness of a derived functor.
def-pc-derived-base-change-map vs lem-weil-pbc-exact-functor-bounded-below: the new node defines the canonical base-change morphism; the existing node is a bounded-below exactness result.
def-pc-derived-base-change-map vs def-weil-pbc-derived-inverse-image: the new node defines the base-change map in a cartesian square; the existing node defines derived inverse image.
def-pc-derived-base-change-map vs def-weil-pbc-derived-square-iso: the new node defines a morphism; the existing node defines an isomorphism attached to a derived square.
def-pc-derived-base-change-map vs def-weil-pbc-adjunction-mate: the new node specializes the mate construction to the base-change morphism; the existing node defines the generic mate operation.
def-pc-derived-base-change-map vs def-weil-pbc-four-arrows: the new node defines the derived base-change arrow; the existing node packages four arrows in a different comparison diagram.
def-pc-derived-base-change-map vs prop-weil-pbc-derived-inverse-image-adjunction: the new node defines base-change using an adjunction; the existing proposition establishes the inverse-image/direct-image adjunction.
def-pc-derived-base-change-map vs lem-weil-pbc-finite-level-rectangle: the new node defines the derived base-change map; the existing lemma proves a finite-level rectangle commutes.
def-pc-derived-base-change-map vs lem-weil-pbc-exchange-forget-coefficients: the new node concerns scheme derived base change; the existing lemma concerns exchange with forgetting coefficients.
def-pc-derived-base-change-map vs lem-weil-pbc-etale-underived-exchange-restriction: the new node is derived and general; the existing lemma is underived and etale-specific.
lem-pc-derived-mayer-vietoris-functorial vs lem-pc-derived-mayer-vietoris-triangle: the existing node asserts existence and identifies the first two maps, while the new node asserts functoriality of the defining short exact sequences, including the connecting map and affine direct-image compatibility.

- Item statement: checked against Tag 0DJ9 and the uses in the relative Mayer--Vietoris gluing node; repaired the previously implicit type of `K'` and explicitly introduced the primed cover `U'` and `V'`.
- Step 1: checked against the hypotheses of `lem-pc-derived-mayer-vietoris-triangle` and the composition statement `lem-pc-derived-direct-image-composition`; verdict sound, with affine-base hypotheses supplying the primed-cover conditions.
- Step 2: checked componentwise against the Mayer--Vietoris arrow descriptions and the definitions of derived pullback and direct image; verdict sound, with the stated restriction naturality supplying the component equalities.
- New nodes are not duplicates: the functoriality node adds the connecting map and affine pushforward compatibility absent from the MV existence node; the base-change definition supplies the canonical morphism absent from the Cech-specific node. Both were searched with LeanFinder, Loogle, and grep and found no Mathlib match.
- Changes: repaired all three returned points, made `K'` explicit, and retained the primed-cover definitions.

## Second reading by G1

- Item statement: checked against Stacks Tag 0DJ9 in `perfect.tex`, including the cartesian square, affine bases, quasi-compact cover, all four base-changed opens, and the three comparison maps; verdict: repaired missing declarations of `K'`, `U'`, and `V'`.
- Step 1: checked against the Tag 0DJ9 induction clause, the derived Mayer--Vietoris statement, and direct-image composition; verdict: the affine hypotheses imply the primed opens are quasi-compact and the displayed identifications supply the triangle terms.
- Step 2: checked against Cohomology Tag 08BV and the base-change construction at Tags 07A7 and 0736; verdict: repaired the map description to use the given `L(g')^*K -> K'` and made the connecting-map argument explicit through the functoriality node.
- `lem-pc-derived-mayer-vietoris-functorial`: checked against Tag 08BV and searched existing DAG nodes plus LeanFinder, Loogle, and Mathlib grep; verdict: genuine auxiliary statement, repaired undefined underived `h^*` to `Lh^*` and added its pullback definition dependency.
- `def-pc-derived-base-change-map`: checked against Tags 07A7 and 0736 and searched existing DAG nodes plus LeanFinder, Loogle, and Mathlib grep; verdict: genuine definition of the canonical adjoint base-change morphism, self-contained and statement-only.
- Small cases: the zero complex gives the zero triangle and commuting zero maps; affine schemes and the empty open intersection reduce to the same functorial short exact sequence construction, so no extra hypothesis is hidden.
- Changes made: restored the missing primed-cover and coefficient-object declarations, corrected the functoriality input and restricted morphism in Step 2, and recorded the additional derived-pullback dependency.
