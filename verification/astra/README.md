# Davidson ve Kazazi hesaplarının bağımsız denetimi

26 Kasım 2026. İncelenen iki çalışma Efe Çam'a aittir. Aşağıdaki kodlar bu incelemede yazıldı. Davidson denetimi depodaki rasyonel sertifikayı girdi olarak kullanır. Kazazi'nin 12 tepeli durumunu denetleyen kodlar Kazazi deposundaki büyük graf taramasını veya sonuç dosyalarını girdi olarak kullanmaz.

## Sürümler ve çalıştırma

Python 3.12, SymPy, bir C++17 derleyicisi ve nauty'nin `geng` programı gerekir. Bu incelemede kullanılan nauty kaynak sürümü `lonnen/nauty` deposunun `3915d891af81630853ab485f2696828a31253cd9` commit'idir. Komutları bu dosyanın bulunduğu dizinde çalıştırın. `geng` komutunun adı sisteminizde `nauty-geng` olabilir. Python'u normal modda çalıştırın. Denetçiler Python'un `assert` komutunu kullanır.

```sh
git clone https://github.com/the-arma-of-owl/davidson-conjecture-4-3-counterexample davidson
git -C davidson checkout 9f2a8de8cb297b35af3b8e05e2bf541d12ef7e4b
git clone https://github.com/the-arma-of-owl/kazazi-backbite-asymptotic kazazi
git -C kazazi checkout 9178b05de73a2b6ae685ce365b87dc1c995de49e

python davidson.py davidson
python count_graphs.py
python path_examples.py
c++ -std=c++17 -O3 minimal.cpp -o minimal
c++ -std=c++17 -O3 descent.cpp -o descent
python check12.py geng ./minimal
python kazazi/code/aday.py ladder 12 | ./descent
python kazazi/code/aday.py d13 12 | ./descent
```

İkinci deponun 10 ve 11 tepeli taramasını yeniden çalıştırmak için aşağıdaki komutları kullandım. Nauty her izomorfizma sınıfı için bir temsilci verir. `-s` seçeneği Hamilton yolunun karesini içeren graflara Kazazi'nin bilinen teoremini uygular.

```sh
cc -O3 kazazi/code/bbconn.c -o bbconn
geng -q -d5 10 | ./bbconn -s
geng -q -d6 11 | ./bbconn -s
```

## Davidson sertifikası

Polinom katsayıları denetleyiciye açıkça yazıldı. Polinomun rasyoneller üzerinde indirgenemezliği, iz polinomu özdeşliği ve iz polinomunun (−2,2) aralığındaki altı kökü sembolik olarak kontrol edilir. Bu özdeşlik, asıl polinomun on iki kökünün birim çemberde olduğunu gösterir. İlkel ve indirgenemez polinomun baş katsayısı 2 olduğu için kökleri cebirsel tamsayı olamaz.

K=78 için ilk 12 rasyonel değerden başlayarak kalan bütün koordinatları bağıntıdan yeniden ürettim. 67 eşitliği sağlayan 79 koordinatın en büyük mutlak değeri yaklaşık 0,9926862486951674 çıktı.

K=79 denetçisinde bütün afin biçimlerin katsayıları ortak bir 2⁶⁸ ölçeğinde tamsayı olarak hesaplanır. Her düğümde önceki kısıtların rasyonel doğrusal kombinasyonu ve başlangıç küpü üzerindeki mutlak değer toplamı kullanılarak üst ve alt sınırlar bulunur. Bu aralıkla kesişen her olası sonraki değerin çocuğu aranır. İşaret simetrisi yalnızca kökte kullanılır. 75.530 düğümün tamamı ziyaret edildi. En büyük derinlik 67 idi. 68 bağıntının birlikte sağlanması imkânsızdır. Depodaki ayrı `verification/referee_code/ref_check.py` de aynı sonucu verdi.

## Kazazi'nin 12 tepeli durumu

**Toplam graf sayısı.** `count_graphs.py` tümleyen graflarda maksimum dereceyi sınırlar ve Burnside lemmasını uygular. Her permütasyonun çevrim tipine göre sabit kalan graflar sayılır. Uzunlukları a,b olan iki farklı çevrim arasında gcd(a,b) kenar yörüngesi vardır. Bir yörüngeyi seçmek birinci çevrimdeki her tepenin derecesini b/gcd(a,b), ikinci çevrimdekilerin derecesini a/gcd(a,b) artırır. Aynı çevrim içindeki kenarlar da döngüsel mesafelerine göre ayrılır. Böylece izomorfizmaya göre toplam sayılar 10, 11 ve 12 tepede sırasıyla 108.376, 868.311 ve 495.369.040 çıkar.

**İskeletlerin bütün grafları kapsaması.** Minimum derecesi en az 6 olan bir graftan, koşulu koruyan kenarları birer birer silin. Sonunda kenar-minimal bir yayılan altgraf kalır. Burada derecesi en az 7 olan iki tepe komşu olamaz. Yüksek dereceli tepelerin sayısı h ise kalan 12−h tepenin her birinin derecesi tam 6'dır. Yüksek dereceli her tepe en az 7 komşusunu bu ikinci kümeden seçtiği için h≤5. h=5 iken yedi alçak dereceli tepenin tamamı beş yüksek dereceli tepenin her birine komşudur. Kendi aralarında 1-düzenli olmaları gerekirdi. Yedi tepede bu olanaksızdır.

`check12.py` alçak dereceli tepelerin indüklediği grafı nauty ile üretir. Bu graftaki her derece 6−h ile 6 arasındadır ve kenar sayısı en çok ⌊(6(12−h)−7h)/2⌋'dir. `minimal.cpp` eksik komşulukları tamamlar, yüksek tepelerin etiket permütasyonlarını ayıklar ve üç iskeletten birinin açık bir yerleştirmesini arar. Alçak tepelerin otomorfizmaları bazı eşbiçimli tamamlamaları tekrar üretebilir. Tablo, denetlenen tamamlama sayısını verir.

| h | Denetlenen tamamlama | İskeletsiz |
|---|---:|---:|
| 0 | 7.849 | 0 |
| 1 | 41.905 | 0 |
| 2 | 126.247 | 0 |
| 3 | 9.918 | 0 |
| 4 | 95 | 0 |
| 5 | 0 | 0 |
| Toplam | 186.014 | 0 |

Bir iskelet kenar-minimal altgrafta bulununca, başlangıçtaki grafta da aynı yerleştirme geçerlidir. Burada kullanılan monoton özellik, iskeletin içerilmesidir. Genel bir grafın yeniden yapılandırma bağlantılılığının her kenar eklemesinde korunacağını varsaymaya gerek yoktur.

**İskeletlerin yeterliliği.** Hamilton yolunun karesi için Kazazi'nin yayılan kare-yol teoremi geçerlidir. Merdiven ve d₁₃ için `path_examples.py` iskeletin kendi Hamilton yollarının (sırasıyla 32 ve 321 yol) tek bileşende olduğunu doğrular. `descent.cpp` ise her bir iskelet için 12!/2 = 239.500.800 sıralamayı dolaşır. Her adımda iskelete ait bir kenar eklenir. İskelete ait olmayan kenarların sayısını en az bir azaltan bir hamleye, merdivende en çok dört, d₁₃'te en çok üç nötr hamleden sonra ulaşılabildi. Bu işlemi tekrarlayan her sıralama bir iskelet yoluna varır. Başlangıçtaki yol daha büyük bir grafın yoluysa bütün ara yollar da o grafın yollarıdır. Bu iki denetim birlikte her iskeletin onu yayılan altgraf olarak içeren graflarda bağlantılılığı sağladığını gösterir.

**Diğer sonuçlar.** 10 tepede kare-yol dışındaki 1.080 graf, 11 tepede 281 graf doğrudan taramadan geçti. Hiçbirinde bağlantısızlık çıkmadı. 10 tepeli seyrek Hamilton grafı için bileşen boyutları 18 ve 4 çıktı. Yol karelerinin yeniden yapılandırma çapları 4'ten 18 tepeye kadar sırasıyla 3, 3, 5, 6, 7, 8, 10, 11, 12, 14, 15, 16, 18, 19, 21 çıktı.

Bu kontroller 12 tepeli sonlu sonucu yeniden üretir. Büyük n için teorem ayrı bir yazılı ispata dayanır. Bu paket Lean formalizasyonu içermez.
