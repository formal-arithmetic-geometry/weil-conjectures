+++
id = "rem-ptr-weil-pbc-derived-inverse-limit-10"
kind = "remark"
title = "Pointer to the derived product notation"
order = 1245
uses = ["def-weil-pbc-derived-inverse-limit", "prop-weil-pbc-derived-product-representation"]
+++
In the notation of [def-weil-pbc-derived-inverse-limit], the following holds.
The derived product

$$
 R\!\prod_nM_n
$$

denotes the product of the system $(\operatorname{ev}_nM_\bullet)$ in
$D(T_{\Proet},A)$, whose representation by
$\prod_n\operatorname{ev}_n(I_\bullet)$ is
[prop-weil-pbc-derived-product-representation].

(*Source note:* the definition is that of Stacks Project, Derived Categories,
Definition 13.34.1 (Tag [08TC](https://stacks.math.columbia.edu/tag/08TC)):
for an inverse system $(K_n,f_n)$ in a triangulated category whose products
exist, an object $K$ is a derived limit if there is a distinguished triangle
$K\to\prod_nK_n\to\prod_nK_n\to K[1]$ whose middle map is
$(k_n)\mapsto(k_n-f_{n+1}(k_{n+1}))$.)
