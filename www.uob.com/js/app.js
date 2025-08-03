;(function(h,j,e){var a="placeholder" in j.createElement("input");var f="placeholder" in j.createElement("textarea");var k=e.fn;var d=e.valHooks;var b=e.propHooks;var m;var l;if(a&&f){l=k.placeholder=function(){return this};l.input=l.textarea=true}else{l=k.placeholder=function(){var n=this;n.filter((a?"textarea":":input")+"[placeholder]").not(".placeholder").bind({"focus.placeholder":c,"blur.placeholder":g}).data("placeholder-enabled",true).trigger("blur.placeholder");return n};l.input=a;l.textarea=f;m={get:function(o){var n=e(o);var p=n.data("placeholder-password");if(p){return p[0].value}return n.data("placeholder-enabled")&&n.hasClass("placeholder")?"":o.value},set:function(o,q){var n=e(o);var p=n.data("placeholder-password");if(p){return p[0].value=q}if(!n.data("placeholder-enabled")){return o.value=q}if(q==""){o.value=q;if(o!=j.activeElement){g.call(o)}}else{if(n.hasClass("placeholder")){c.call(o,true,q)||(o.value=q)}else{o.value=q}}return n}};if(!a){d.input=m;b.value=m}if(!f){d.textarea=m;b.value=m}e(function(){e(j).delegate("form","submit.placeholder",function(){var n=e(".placeholder",this).each(c);setTimeout(function(){n.each(g)},10)})});e(h).bind("beforeunload.placeholder",function(){e(".placeholder").each(function(){this.value=""})})}function i(o){var n={};var p=/^jQuery\d+$/;e.each(o.attributes,function(r,q){if(q.specified&&!p.test(q.name)){n[q.name]=q.value}});return n}function c(o,p){var n=this;var q=e(n);if(n.value==q.attr("placeholder")&&q.hasClass("placeholder")){if(q.data("placeholder-password")){q=q.hide().next().show().attr("id",q.removeAttr("id").data("placeholder-id"));if(o===true){return q[0].value=p}q.focus()}else{n.value="";q.removeClass("placeholder");n==j.activeElement&&n.select()}}}function g(){var r;var n=this;var q=e(n);var p=this.id;if(n.value==""){if(n.type=="password"){if(!q.data("placeholder-textinput")){try{r=q.clone().attr({type:"text"})}catch(o){r=e("<input>").attr(e.extend(i(this),{type:"text"}))}r.removeAttr("name").data({"placeholder-password":q,"placeholder-id":p}).bind("focus.placeholder",c);q.data({"placeholder-textinput":r,"placeholder-id":p}).before(r)}q=q.removeAttr("id").hide().prev().attr("id",p).show()}q.addClass("placeholder");q[0].value=q.attr("placeholder")}else{q.removeClass("placeholder")}}}(this,document,jQuery));

/* Modernizr 2.6.2 (Custom Build) | MIT & BSD
 * Build: http://modernizr.com/download/#-touch-cssclasses-teststyles-prefixes
 */
;window.Modernizr=function(a,b,c){function w(a){j.cssText=a}function x(a,b){return w(m.join(a+";")+(b||""))}function y(a,b){return typeof a===b}function z(a,b){return!!~(""+a).indexOf(b)}function A(a,b,d){for(var e in a){var f=b[a[e]];if(f!==c)return d===!1?a[e]:y(f,"function")?f.bind(d||b):f}return!1}var d="2.6.2",e={},f=!0,g=b.documentElement,h="modernizr",i=b.createElement(h),j=i.style,k,l={}.toString,m=" -webkit- -moz- -o- -ms- ".split(" "),n={},o={},p={},q=[],r=q.slice,s,t=function(a,c,d,e){var f,i,j,k,l=b.createElement("div"),m=b.body,n=m||b.createElement("body");if(parseInt(d,10))while(d--)j=b.createElement("div"),j.id=e?e[d]:h+(d+1),l.appendChild(j);return f=["&#173;",'<style id="s',h,'">',a,"</style>"].join(""),l.id=h,(m?l:n).innerHTML+=f,n.appendChild(l),m||(n.style.background="",n.style.overflow="hidden",k=g.style.overflow,g.style.overflow="hidden",g.appendChild(n)),i=c(l,a),m?l.parentNode.removeChild(l):(n.parentNode.removeChild(n),g.style.overflow=k),!!i},u={}.hasOwnProperty,v;!y(u,"undefined")&&!y(u.call,"undefined")?v=function(a,b){return u.call(a,b)}:v=function(a,b){return b in a&&y(a.constructor.prototype[b],"undefined")},Function.prototype.bind||(Function.prototype.bind=function(b){var c=this;if(typeof c!="function")throw new TypeError;var d=r.call(arguments,1),e=function(){if(this instanceof e){var a=function(){};a.prototype=c.prototype;var f=new a,g=c.apply(f,d.concat(r.call(arguments)));return Object(g)===g?g:f}return c.apply(b,d.concat(r.call(arguments)))};return e}),n.touch=function(){var c;return"ontouchstart"in a||a.DocumentTouch&&b instanceof DocumentTouch?c=!0:t(["@media (",m.join("touch-enabled),("),h,")","{#modernizr{top:9px;position:absolute}}"].join(""),function(a){c=a.offsetTop===9}),c};for(var B in n)v(n,B)&&(s=B.toLowerCase(),e[s]=n[B](),q.push((e[s]?"":"no-")+s));return e.addTest=function(a,b){if(typeof a=="object")for(var d in a)v(a,d)&&e.addTest(d,a[d]);else{a=a.toLowerCase();if(e[a]!==c)return e;b=typeof b=="function"?b():b,typeof f!="undefined"&&f&&(g.className+=" "+(b?"":"no-")+a),e[a]=b}return e},w(""),i=k=null,e._version=d,e._prefixes=m,e.testStyles=t,g.className=g.className.replace(/(^|\s)no-js(\s|$)/,"$1$2")+(f?" js "+q.join(" "):""),e}(this,this.document);
Modernizr.addTest('android',function(){return!!navigator.userAgent.match(/Android/i)});
Modernizr.addTest('chrome',function(){return!!navigator.userAgent.match(/Chrome/i)});
Modernizr.addTest('firefox',function(){return!!navigator.userAgent.match(/Firefox/i)});
Modernizr.addTest('iemobile',function(){return!!navigator.userAgent.match(/IEMobile/i)});
Modernizr.addTest('ie',function(){return!!navigator.userAgent.match(/MSIE/i)});
Modernizr.addTest('ie8',function(){return!!navigator.userAgent.match(/MSIE 8/i)});
Modernizr.addTest('ie10',function(){return!!navigator.userAgent.match(/MSIE 10/i)});
Modernizr.addTest('ie11',function(){return!!navigator.userAgent.match(/Trident.*rv:11\./)});
Modernizr.addTest('ios',function(){return!!navigator.userAgent.match(/iPhone|iPad|iPod/i)});
Modernizr.addTest('iosmobile',function(){return!!navigator.userAgent.match(/iPhone|iPod/i)});
Modernizr.addTest('iostablet',function(){return!!navigator.userAgent.match(/iPad/i)});

Modernizr.addTest('tablet',function(){
    return (Modernizr.iostablet || (Modernizr.android && ($(window).width() > 767)))
});

Modernizr.addTest('phone',function(){
    return (Modernizr.iosmobile || (Modernizr.android && ($(window).width() < 768)))
});

/*!
* screenfull
* v1.0.4 - 2013-05-26
* https://github.com/sindresorhus/screenfull.js
* (c) Sindre Sorhus; MIT License
*/
(function(a,b){"use strict";var c="undefined"!=typeof Element&&"ALLOW_KEYBOARD_INPUT"in Element,d=function(){for(var a,c,d=[["requestFullscreen","exitFullscreen","fullscreenElement","fullscreenEnabled","fullscreenchange","fullscreenerror"],["webkitRequestFullscreen","webkitExitFullscreen","webkitFullscreenElement","webkitFullscreenEnabled","webkitfullscreenchange","webkitfullscreenerror"],["webkitRequestFullScreen","webkitCancelFullScreen","webkitCurrentFullScreenElement","webkitCancelFullScreen","webkitfullscreenchange","webkitfullscreenerror"],["mozRequestFullScreen","mozCancelFullScreen","mozFullScreenElement","mozFullScreenEnabled","mozfullscreenchange","mozfullscreenerror"]],e=0,f=d.length,g={};f>e;e++)if(a=d[e],a&&a[1]in b){for(e=0,c=a.length;c>e;e++)g[d[0][e]]=a[e];return g}return!1}(),e={request:function(a){var e=d.requestFullscreen;a=a||b.documentElement,/5\.1[\.\d]* Safari/.test(navigator.userAgent)?a[e]():a[e](c&&Element.ALLOW_KEYBOARD_INPUT)},exit:function(){b[d.exitFullscreen]()},toggle:function(a){this.isFullscreen?this.exit():this.request(a)},onchange:function(){},onerror:function(){},raw:d};return d?(Object.defineProperties(e,{isFullscreen:{get:function(){return!!b[d.fullscreenElement]}},element:{enumerable:!0,get:function(){return b[d.fullscreenElement]}},enabled:{enumerable:!0,get:function(){return!!b[d.fullscreenEnabled]}}}),b.addEventListener(d.fullscreenchange,function(a){e.onchange.call(e,a)}),b.addEventListener(d.fullscreenerror,function(a){e.onerror.call(e,a)}),a.screenfull=e,void 0):a.screenfull=!1})(window,document);


// data-shift api 
+function ($) { "use strict";

 /* SHIFT CLASS DEFINITION
  * ====================== */

  var Shift = function (element) {
    this.$element = $(element)
    this.$prev = this.$element.prev()
    !this.$prev.length && (this.$parent = this.$element.parent())
  }

  Shift.prototype = {
  	constructor: Shift

    , init:function(){
    	var $el = this.$element
    	, method = $el.data()['toggle'].split(':')[1]    	
    	, $target = $el.data('target')
    	$el.hasClass('in') || $el[method]($target).addClass('in')
    }
    , reset :function(){
    	this.$parent && this.$parent['prepend'](this.$element)
    	!this.$parent && this.$element['insertAfter'](this.$prev)
    	this.$element.removeClass('in')
    }
  }

 /* SHIFT PLUGIN DEFINITION
  * ======================= */

  $.fn.shift = function (option) {
    return this.each(function () {
      var $this = $(this)
        , data = $this.data('shift')
      if (!data) $this.data('shift', (data = new Shift(this)))
      if (typeof option == 'string') data[option]()
    })
  }

  $.fn.shift.Constructor = Shift
}(jQuery);


// data-bjax api 
+function ($) { "use strict";
  var Bjax = function (element, options) {
    this.options   = options
    this.$element  = $(element)
    this.start()
  }

  Bjax.DEFAULTS = {
      backdrop: true
    , url: ''
  }

  Bjax.prototype.start = function () {
    var that = this;
    this.backdrop();
    $.ajax(this.options.url).done(function(r){
      that.$content = r;
      that.complete();
    });
  }

  Bjax.prototype.complete = function (){
    var that = this;
    try{
      window.history.pushState({}, '', this.options.url);
    }catch(e){
      window.location.replace(this.options.url)
    }

    this.updateBar(100);    
  }

  Bjax.prototype.backdrop = function(){
    this.$element.css('position','relative')
    this.$backdrop = $('<div class="backdrop fade"></div>')
      .appendTo(this.$element);

    this.$backdrop[0].offsetWidth; // force reflow
    this.$backdrop.addClass('in');

    this.$bar = $('<div class="bar b-t b-info"></div>')
      .width(0)
      .appendTo(this.$backdrop);
  }

  Bjax.prototype.update = function (){
    !this.$element.is('html') && this.$element.html(this.$content);
    if( this.$element.is('html') ) {
      document.open();
      document.write(this.$content);
      document.close();
    }
  }

  Bjax.prototype.updateBar = function (per){ 
    var that = this;
    this.$bar.stop().animate({
        width: per + '%'
    }, 500, 'linear', function(){
      if(per == 100) that.update();
    });
  }

  Bjax.prototype.enable = function (e){
    var link = e.currentTarget;
    if ( location.protocol !== link.protocol || location.hostname !== link.hostname )
      return false
    if (link.hash && link.href.replace(link.hash, '') ===
         location.href.replace(location.hash, ''))
      return false
    if (link.href === location.href + '#' || link.href === location.href || (location.href.indexOf(link.href) !=-1) )
      return false
    return true;
  }

  $.fn.bjax = function (option) {
    return this.each(function () {
      var $this   = $(this);
      var data    = $this.data('app.bjax');
      var options = $.extend({}, Bjax.DEFAULTS, $this.data(), typeof option == 'object' && option)

      if (!data) $this.data('app.bjax', (data = new Bjax(this, options)))
      if (typeof option == 'string') data[option]()
    })
  }

  $.fn.bjax.Constructor = Bjax

  $(window).on("popstate", function(e) {
    if (e.originalEvent.state !== null) {
      window.location.reload(true);
    }
    e.preventDefault();
  });

//  $(document).on('click.app.bjax.data-api', '[data-bjax], .nav-primary a', function (e) {
//    if(!Bjax.prototype.enable(e)) return;
//    var $this   = $(this);
//    var $url    = $this.attr('href');
//    var $target = $( $this.attr('data-target') || 'html' );
//    var option  = $.extend({ url: $url }, $target.data(), $this.data());
//    $target.bjax(option);
//    e.preventDefault();
//  })
}(jQuery);

Date.now = Date.now || function() { return +new Date; };

function setCookie(cname, cvalue, exdays) {
    var d = new Date();
    d.setTime(d.getTime() + (exdays*24*60*60*1000));
    var expires = "expires="+d.toGMTString();
    document.cookie = cname + "=" + cvalue + "; " + expires;
}

function getCookie(cname) {
    var name = cname + "=";
    var ca = document.cookie.split(';');
    for(var i=0; i<ca.length; i++) {
        var c = ca[i].trim();
        if (c.indexOf(name) == 0) return c.substring(name.length,c.length);
    }
    return "";
}

var renderTimeline = renderTimeline || null;
if (document.getElementById('nav') !== null) {
if (Modernizr.tablet) {
    if (getCookie('firstTimeLogin') !== 'true') {
        setTimeout(function(){
            document.getElementById('nav').className = document.getElementById('nav').className + ' nav-xs';
            document.getElementById('nav-footer-toggle').className = document.getElementById('nav-footer-toggle').className + ' active';
            setCookie('firstTimeLogin', true, 10000);
            if (renderTimeline) {
              renderTimeline();
            }
        }, 5000);
    } else {
        document.getElementById('nav').className = document.getElementById('nav').className + ' nav-xs';
        document.getElementById('nav-footer-toggle').className = document.getElementById('nav-footer-toggle').className + ' active';
        if (renderTimeline) {
          renderTimeline();
        }
    }
}
}


+function ($) {

  $(function(){

      $('.blocker-container').removeClass('loading');

      $(".as_of_today").html("AS OF " + moment().format("DD-MMM-YYYY"));
      $('#btn-sidebar').attr('data-toggle', 'class:show');

      $('#btn-sidebar').on('click', function(){
        widgetAccordionReset($(this));
          setTimeout(function(){
            if (renderTimeline) {
              renderTimeline();
            }
          }, 100);

      });

      $('#nav-footer-toggle').on('click', function() {
          setTimeout(function(){
            if (renderTimeline) {
              renderTimeline();
            }
          }, 1);
      });

      $('[data-validate="parsley"]').each(function () {
          $(this).parsley();

          $(this).submit(function(e){
              if (true === $(this).parsley().validate()) {
                  if ($(this).hasClass('success-available')) {
                    gotoNextFormStep($(this).parent().parent(), 'step-2');
                      $(this).find('input').val('');
                      $(this).find('select').val('');
                  } else if ($(this).hasClass('confirm-success-available')) {
                      if ($(this).hasClass('active')) {
                          gotoNextFormStep($(this).parent().parent(), 'step-2');
                          $(this).find('input:not([type=submit])').val('');
                          $(this).find('select').val('');
                          $(this).find('.item-cancel').click();
                      } else {
                          $(this).find('.mode-edit .item-input').each(function () {
                              if ($(this).parent().parent().find('.mode-preview input').val() !== undefined) {
                                  $(this).text($(this).parent().parent().find('.mode-preview input').val());
                              } else if ($(this).parent().parent().find('.mode-preview select').val() !== undefined) {
                                  $(this).text($(this).parent().parent().find('.mode-preview select').val());
                              }
                          });
                          $(this).find('.item-edit').click();
                      }
                  } else if ($(this).hasClass('inline-update')) {
                      $(this).find('input:not([type=submit])').val('');
                      $(this).find('select').val('');
                      pageNotification('success', $(this).data('success'));
                      $(this).find('.item-cancel').click();
                  } else {
                      return true;
                  }
              }
              return false;
          });
      });

      $('#acc-widgets .another').on('click', function(){
          gotoNextFormStep($(this).closest('.panel-collapse'), 'step-1');
          $(this).closest('.panel-collapse').find('input:not([type=submit]),select').val('');
      });




    $(".level-one li.activate").hover(function(){
        showPopNav($(this));
    });

    $(".level-one > li:not(.activate) > a").hover(function(){
        closePopNav();
    });

    $("#content, header, .dk.nav-user, .level-one li:not(.activate), .footer").hover(function(){
        closePopNav();
    });

      $('input[name="post[]"]').click(function(){
          if ($(this).hasClass('input-panel')) {
              if ($(this).closest('.table-list').length > 0) {
                  if ($(this).closest('.table-list').find('input[name="post[]"]:checked').length === $(this).closest('.table-list').find('input[name="post[]"]').length && $(this).closest('.table-list').find('input[name="post[]"]').length > 0) {
                      $(this).closest('.table-list').find('input[name="post-all"]').prop('checked', true);
                  } else {
                      $(this).closest('.table-list').find('input[name="post-all"]').prop('checked', false);
                  }
              } else {
                  if ($(this).closest('.tables').find('input[name="post[]"]:checked').length === $(this).closest('.tables').find('input[name="post[]"]').length && $(this).closest('.tables').find('input[name="post[]"]').length > 0) {
                      $(this).closest('.tables').find('input[name="post-all"]').prop('checked', true);
                  } else {
                      $(this).closest('.tables').find('input[name="post-all"]').prop('checked', false);
                  }
              }
          } else {
              if ($(this).closest('.tab-pane').find('input[name="post[]"]:checked').length === $(this).closest('.tab-pane').find('input[name="post[]"]').length && $(this).closest('.tab-pane').find('input[name="post[]"]').length > 0) {
                  $(this).closest('.tab-pane').find('input[name="post-all"]').prop('checked', true);
              } else {
                  $(this).closest('.tab-pane').find('input[name="post-all"]').prop('checked', false);
              }
          }

          var checked = $('input[name="post[]"]:checked').length;
          if (checked > 0) {
              $('#selected-account').text(checked);
          }
          $('#footer-action .link-single').toggleClass('hide', checked !== 1);
          $('#footer-action').toggleClass('hide', checked === 0);
      });

      $('input[name="post-all"]').click(function(){
          if ($(this).hasClass('input-panel')) {
              if ($(this).is(':checked')) {
                  $(this).closest('.panel').find('input[name="post[]"]').prop('checked', true);
                  $('#footer-action').removeClass('hide');
              } else {
                  $(this).closest('.panel').find('input[name="post[]"]').prop('checked', false);
                  $('#footer-action').addClass('hide');
              }
          } else {
              if ($(this).is(':checked')) {
                  $(this).closest('.tab-pane').find('input[name="post[]"]').prop('checked', true);
                  $('#footer-action').removeClass('hide');
              } else {
                  $(this).closest('.tab-pane').find('input[name="post[]"]').prop('checked', false);
                  $('#footer-action').addClass('hide');
              }
          }

          var checked = $('input[name="post[]"]:checked').length;
          $('#footer-action .link-single').toggleClass('hide', checked !== 1);
      });

      $('a[data-toggle="tab"]').click(function(){
          $('#footer-action').addClass('hide');
          $('#footer-action .link-single').toggleClass('hide', true);
          $('input[name="post[]"]:checked').each(function(){
             $(this).prop('checked', false);
          });
          $('input[name="post-all"]:checked').each(function(){
              $(this).prop('checked', false);
          });
          $('input[name="selPayeeDtl"]:checked').each(function(){
              $(this).prop('checked', false);
          });
      });

    // toogle fullscreen
    $(document).on('click', "[data-toggle=fullscreen]", function(e){
      e.preventDefault();
      if (screenfull.enabled) {
        screenfull.request();
      }
    });

  	// placeholder
  	$('input[placeholder], textarea[placeholder]').placeholder();

    // popover
    $("[data-toggle=popover]").popover();
    $(document).on('click', '.popover-title .close', function(e){
    	var $target = $(e.target), $popover = $target.closest('.popover').prev();
    	$popover && $popover.popover('hide');
    });

    // ajax modal
    
    $(document).on('click', '[data-toggle*="ajaxModal"]',
      function(e) {
        e.preventDefault();
        var count = $('.ajaxModal').length;
        if (count > 0) {
          $('#ajaxModal' + (count - 1)).toggleClass('in', false);
        }
        var $this = $(this)
          , $remote = $this.data('remote') || $this.attr('href')
          , $modal = $('<div class="modal fade ajaxModal" id="ajaxModal' + $('.ajaxModal').length + '"><div class="modal-body"></div></div>')
          , itemId = ($(this).data('edit') > 0) ? $(this).data('edit') : 0;
        $('body').append($modal);
        $modal.modal();
        $modal.on('hidden.bs.modal', function(e) {
          $modal.remove();
          if (count > 0) {
            $('#ajaxModal' + (count - 1)).toggleClass('in', true);
          }
        });
        $modal.load($remote, function(){
            modalReset($modal.find('.modal-dialog'));
        });
      }
    );
	
// This entire section makes Bootstrap Modals work with iOS
if( navigator.userAgent.match(/iPhone|iPad|iPod/i) ) {
  var scrollLocation;

  $('.modal').on('show.bs.modal', function() {
    setTimeout(function () {
      scrollLocation = $(window).scrollTop();
      $('.modal')
          .addClass('modal-ios')
          .height($(window).height())
          .css({'margin-top': scrollLocation + 'px'});
    }, 0);
  });

  $('input').on('blur', function(){
    setTimeout(function() {
      // This causes iOS to refresh, fixes problems when virtual keyboard closes
      $(window).scrollLeft(0);

      var $focused = $(':focus');
      // Needed in case user clicks directly from one input to another
      if(!$focused.is('input') && scrollLocation) {
        // Otherwise reset the scoll to the top of the modal
        $(window).scrollTop(scrollLocation);
      }
    }, 0);
  })

}

      $(document).on('click', '[data-toggle="collapse"]', function(){
        footerSet();
      });

      $(document).on('click', '.modal-dialog [data-toggle="tab"]', function(){
        modalReset($('.modal-dialog'));
      });


      $.fn.dropdown.Constructor.prototype.change = function(e){
          e.preventDefault();
          var $item = $(e.target), $select, $checked = false, $menu, $label;
          !$item.is('a') && ($item = $item.closest('a'));
          $menu = $item.closest('.dropdown-menu');
          $label = $menu.parent().find('.dropdown-label');
          $labelHolder = $label.text();
          $select = $item.find('input');
          $checked = $select.is(':checked');
          if($select.is(':disabled')) return;
          if($select.attr('type') == 'radio' && $checked) return;
          if($select.attr('type') == 'radio') $menu.find('li').removeClass('active');
          $item.parent().removeClass('active');
          !$checked && $item.parent().addClass('active');
          $select.prop("checked", !$select.prop("checked"));

          $items = $menu.find('li > a > input:checked');
          if ($items.length) {
              $text = [];
              $items.each(function () {
                  var $str = $(this).parent().text();
                  $str && $text.push($.trim($str));
              });

              $text = $text.length < 4 ? $text.join(', ') : $text.length + ' selected';
              $label.html($text);
          }else{
              $label.html($label.data('placeholder'));
          }
          if ($(this).closest('.btn-group').hasClass('select-repeat')) {
              $('.popover').prev().popover('hide');
              if ($text === 'Yes' ) {
                  $(this).closest('.detail-block').find("input[name=fast-transfer]").prop('checked', false);
                  $(this).closest('.detail-block').find("input[name=fast-transfer]").prop( "disabled", true);
                  $(this).closest('.detail-block').find(".purpose-text").addClass( "hidden");
                  $(this).closest('.detail-block').find(".purpose-label").addClass( "hidden");
                  if ($(this).closest('.btn-group').parent().find('.popover').attr('class') === undefined) {
                      $(this).closest('.btn-group').parent().find('.repeat-frequency').click();
                  }
              } else {

                  $(this).closest('.detail-block').find("input[name=fast-transfer]").prop( "disabled", false);
                  $(this).closest('.btn-group').parent().find('.frequency-text').addClass('hidden');
                  if ($(this).closest('.btn-group').parent().find('.popover').attr('class') !== undefined) {
                      $(this).closest('.btn-group').parent().find('.repeat-frequency').click();
                  }
              }
          }
          $(document).on('change', '.checkboxClass', function(){
              $(this).closest('.rows').find('.transfer-fields').toggleClass('hidden', !$(this).is(':checked'));
              $(this).closest('.rows').find('.no-transfer-fields').toggleClass('hidden', $(this).is(':checked'));
          });
          if ($(this).closest('.btn-group').hasClass('select-oversea-use')) {
              $('.popover').prev().popover('hide');
              if ($text === 'Yes' ) {
                  if ($(this).closest('.btn-group').parent().find('.popover').attr('class') === undefined) {
                      $(this).closest('.btn-group').parent().find('.oversea-use').click();
                      $(".datepicker-input").each(function(){
                        $(this).datepicker({
                            autoclose: true
                        });
                        $(this).before('<div class="datepicker-calendar"><img src="../resources/images/icon-datepicker.html"></div>');
                      });
                  }
              } else {
                  $(this).closest('.btn-group').parent().find('.oversea-text').addClass('hidden');
                  if ($(this).closest('.btn-group').parent().find('.popover').attr('class') !== undefined) {
                      $(this).closest('.btn-group').parent().find('.oversea-use').click();
                  }
              }
          }
      }

      $(document).mouseup(function (e)
      {
          var container = $('.popover'),
              datepick = $('.datepicker');

          if (!container.is(e.target) // if the target of the click isn't the container...
              && container.has(e.target).length === 0
              && !datepick.is(e.target)
              && datepick.has(e.target).length === 0) // ... nor a descendant of the container
          {
              $('.popover').prev().popover('hide');
          }
      });

    $(document).on('click.dropdown-menu', '.dropdown-select > li > a', $.fn.dropdown.Constructor.prototype.change);

    $(document).on('change','.popover-content .popup-select-frequency select', function(){
        var $parent = $(this).closest('.form-group'),
            $frequency = $(this).parent().find('.sel-frequency').val(),
            $number = $(this).parent().find('.sel-number').val(),
            $frequencyPopup = $(this).closest('.popover');
        if ($frequency !== '' && $number !== '') {
            $parent.find('input[name=frequency]').val($frequency);
            $parent.find('input[name=number]').val($number);
            $parent.find('.frequency-text').text($frequency + ' - ' + $number + ' times');
            $parent.find('.frequency-text').removeClass('hidden');
            $frequencyPopup.find('.close').click();
        }
    })

      $(document).on('click', '.oversea-submit', function(){
          var $repeatFrequency = $(this).closest('.form-group'),
              $frequencyPopup = $(this).closest('.popover');
          if ($(this).parent().find('.start-date').val() !== '' && $(this).parent().find('.end-date').val() !== '') {
              $repeatFrequency.find('input[name=start-date]').val($(this).parent().find('.start-date').val());
              $repeatFrequency.find('input[name=end-date]').val($(this).parent().find('.end-date').val());
              $repeatFrequency.find('.oversea-text').html(moment($(this).parent().find('.start-date').val(), 'DD-MM-YYYY').format("DD MMM YYYY") + ' - ' + moment($(this).parent().find('.end-date').val(), 'DD-MM-YYYY').format("DD MMM YYYY"));
              $repeatFrequency.find('.oversea-text').removeClass('hidden');
              $frequencyPopup.prev().popover('hide');
          }
      })

    $(document).on('change', 'input[name=fast-transfer]', function(){
        if ($(this).is(':checked')) {
            if ($(this).closest('.form-group').parent().find('.popover').attr('class') === undefined) {
                $(this).closest('.form-group').parent().find('.fast-purpose').click();
            }
        } else {
            $(this).closest('.detail-block').find('.purpose-text').addClass('hidden');
            $(this).closest('.detail-block').find('.purpose-label').addClass('hidden');
            if ($(this).closest('.form-group').parent().find('.popover').attr('class') !== undefined) {
                $(this).closest('.form-group').parent().find('.fast-purpose').click();
            }
        }
    });

      $(document).on('change','.popover-content .popup-select-purpose select', function(){
          var $repeatFrequency = $(this).closest('.form-group').find('.fast-purpose'),
              $frequencyPopup = $(this).closest('.popover');
          if ($(this).parent().find('.sel-purpose').val() !== '') {
              var parent = $repeatFrequency.closest('.detail-block');
              parent.find('input[name=purpose]').val($(this).parent().find('.sel-purpose').val());
              parent.find('.purpose-text').text('Waived - ' + $(this).parent().find('.sel-purpose').val());
              parent.find('.purpose-text').removeClass('hidden');
              parent.find('.purpose-label').removeClass('hidden');
              $frequencyPopup.find('.close').click();
          }
      })

  	// tooltip
    $("[rel*=tooltip]").tooltip();
    $(".tooltip-click").tooltip({trigger:'click'});

    // class
  	$(document).on('click', '[data-toggle^="class"]', function(e){
  		e && e.preventDefault();
  		var $this = $(e.target), $class , $target, $tmp, $classes, $targets;
  		!$this.data('toggle') && ($this = $this.closest('[data-toggle^="class"]'));
    	$class = $this.data()['toggle'];
    	$target = $this.data('target') || $this.attr('href');
      $class && ($tmp = $class.split(':')[1]) && ($classes = $tmp.split(','));
      $target && ($targets = $target.split(','));
      $classes && $classes.length && $.each($targets, function( index, value ) {
        if ( $classes[index].indexOf( '*' ) !== -1 ) {
          var patt = new RegExp( '\\s' + 
              $classes[index].
                replace( /\*/g, '[A-Za-z0-9-_]+' ).
                split( ' ' ).
                join( '\\s|\\s' ) + 
              '\\s', 'g' );
          $($this).each( function ( i, it ) {
            var cn = ' ' + it.className + ' ';
            while ( patt.test( cn ) ) {
              cn = cn.replace( patt, ' ' );
            }
            it.className = $.trim( cn );
          });
        }
        ($targets[index] !='#') && $($targets[index]).toggleClass($classes[index]) || $this.toggleClass($classes[index]);
      });
    	$this.toggleClass('active');
  	});

    // panel toggle
    $(document).on('click', '.panel-toggle', function(e){
      e && e.preventDefault();
      var $this = $(e.target), $class = 'collapse' , $target;
      if (!$this.is('a')) $this = $this.closest('a');
      $target = $this.closest('.panel');
        $target.find('.panel-body').toggleClass($class);
        $this.toggleClass('active');
    });
  	
  	// carousel
  	$('.carousel.auto').carousel();
  	
  	// button loading
  	$(document).on('click.button.data-api', '[data-loading-text]', function (e) {
  	    var $this = $(e.target);
  	    $this.is('i') && ($this = $this.parent());
  	    $this.button('loading');
  	});
 	
    var $window = $(window);
    // mobile
  	var mobile = function(option){
  		if(option == 'reset'){
  			$('[data-toggle^="shift"]').shift('reset');
  			return true;
  		}
  		$('[data-toggle^="shift"]').shift('init');
      return true;
  	};
  	// unmobile
  	$window.width() < 768 && mobile();
    // resize
    var $resize;
  	$window.resize(function() {

      clearTimeout($resize);
      $resize = setTimeout(function(){
        setHeight();
        $window.width() < 767 && mobile();
        $window.width() >= 768 && mobile('reset') && fixVbox();
            widgetAccordionReset($('#btn-sidebar'));
          sameHeight();
          footerSet();
      }, 500);
  	});

      $(document).on('click', '.accordion-toggle, #btn-sidebar, [href="#nav"]', function(){
          var timer = 10;
          if ($(this).hasClass('accordion-toggle')) {
              timer = 150;
          }
          setTimeout(sameHeight, timer);
      });



    var default_title = $("#header-sticky h3.visible-xs").html() || $('.panel-header .title').html();

    $(".table-list.newcss .nav-tabs li a").on('click', function(e){
        var ele = $(e.currentTarget ? e.currentTarget : e.srcElement).children('span');
        $(".panel-block").addClass('mobile-nav-left');
        $("#tab-sticky-sticky-wrapper").addClass('mobile-nav-left');
        var text = ele.html().toLowerCase();
        $("#header-sticky h3.visible-xs").html(text);
        $(".panel-header .title .visible-xs").html(text);
        $('.panel-header .sub-title').toggleClass('hidden-xs', true);
        footerSet();
    });

    $(".panel-header").on('click', function() {
        $(".panel-block").removeClass('mobile-nav-left');
        $("#tab-sticky-sticky-wrapper").removeClass('mobile-nav-left');
        $(".panel-header .title .visible-xs").html(default_title);
        $('.panel-header .sub-title').toggleClass('hidden-xs', false);
        footerSet();
    });

    $("#header-sticky h3").on('click', function(){
        $(".panel-block").removeClass('mobile-nav-left');
        $("#tab-sticky-sticky-wrapper").removeClass('mobile-nav-left');
        $("#header-sticky h3.visible-xs").html(default_title);
        footerSet();
    });

    // fluid layout
    var setHeight = function(){
      $('.app-fluid .nav-primary').css('min-height', $(window).height()-60);
      return true;
    }
    setHeight();

    
    // fix vbox
    var fixVbox = function(){
      $('.ie11 .vbox').each(function(){
        $(this).height($(this).parent().height());
      });
      return true;
    }
    fixVbox();

    // collapse nav
    $(document).on('click', '[data-ride="collapse"] a', function (e) {
      var $this = $(e.target), $active;
      $this.is('a') || ($this = $this.closest('a'));
      
      $active = $this.parent().siblings( ".active" );
      $active && $active.toggleClass('active').find('> ul:visible').slideUp(200);
      
      ($this.parent().hasClass('active') && $this.next().slideUp(200)) || $this.next().slideDown(200);
      $this.parent().toggleClass('active');
      
      $this.next().is('ul') && e.preventDefault();

      setTimeout(function(){ $(document).trigger('updateNav'); }, 300);      
    });
	
	// lightbox steps
	$(document).on('click', 'a.popup-step-action', function (e) {
		var goto=$(this).attr('data');
		$('.popup-step').hide();
		$('.popup-step.popup-' + goto).show();
    });
	
	$(document).on('click', 'a.btn-toggle-sh', function (e) {
		$('.toggle-content').toggle();
		if($(this).find('i').hasClass('fa-caret-up')==true)
		{
			$(this).find('i').removeClass('fa-caret-up');
			$(this).find('i').addClass('fa-caret-down');
			$(this).find('strong').text('Show');
		}
		else
		{
			$(this).find('i').removeClass('fa-caret-down');
			$(this).find('i').addClass('fa-caret-up');
			$(this).find('strong').text('Hide');
		}
    });

    // dropdown still
    $(document).on('click.bs.dropdown.data-api', '.dropdown .on, .dropup .on, .open .on', function (e) { e.stopPropagation() });
	
	/*$('[data-validate="parsley"]').each(function () {
        var validated = false;
     */

      // GRID ITEMS

    $('.grid-item .item-full').on('click', function(){

     if ($(this).parent().hasClass('active')) {
       $(this).parent().removeClass('active');
       $(this).parent().find('.mode-preview').removeClass('hidden');
       $(this).parent().find('.mode-edit').addClass('hidden');
     } else {
       $('.grid-item.active').find('.mode-preview').removeClass('hidden');
       $('.grid-item.active').find('.mode-edit').addClass('hidden');
       $('.grid-item.active').removeClass('active');
       $(this).parent().addClass('active');
     }
    });

    $('.grid-item .btn-edit').on('click', function(){
        var grid_item = $(this).closest('.grid-item');
        grid_item.find('.mode-preview').addClass('hidden');
        grid_item.find('.mode-edit').removeClass('hidden');
    });

    $('.grid-item .btn-save, .grid-item .btn-cancel-edit').on('click', function(){
        var grid_item = $(this).closest('.grid-item');
        grid_item.find('.mode-preview').removeClass('hidden');
        grid_item.find('.mode-edit').addClass('hidden');
    });



      // LIST ITEMS
      $('.list-item').on('click', '.item-edit', function(){
          var list_item = $(this).closest('.list-item');
          list_item.addClass('active').addClass('edit');
          list_item.find('.mode-preview').addClass('hidden');
          list_item.find('.mode-edit').removeClass('hidden');
          var live = $(this).parent().find('.item-detail.live');
          if (!live.hasClass('active')) {
            live.click();
          }
          sameHeight();
      });

      $('.list-item .item-resend').on('click', function(){
          var data_resend = $(this).data('resend');
              pageNotification('success', 'You have successfully resend ' + data_resend);
      });

      $('.list-item .item-save, .list-item .item-cancel').on('click', function(){
          var list_item = $(this).closest('.list-item');
          list_item.removeClass('active').removeClass('edit');
          list_item.find('.mode-preview').removeClass('hidden');
          list_item.find('.mode-edit').addClass('hidden');

            if ($(this).hasClass('item-save')) {
                pageNotification('success', 'You have successfully updated an item');
            }
      });

      $('.list-item').on('click', '.item-transaction-login', function(){
          $('#main-body-content').scrollTop(0);
          var list_item = $(this).closest('.list-item'),
              title = $(this).data('title');

          transactionLogin(list_item, title);
      });

      $('.item-action').on('click', '.item-transaction-login', function(){
          $('#main-body-content').scrollTop(0);
          var elem = $(this).closest('.item-action'),
              title = $(this).data('title');

          transactionLogin(elem, title);
      });

      $('form.transaction-login').on('submit', function(){
         $(this).find('.item-transaction-login').click();
          $('#main-body-content').scrollTop(0);
          var title = $(this).data('title');
          if (title !== undefined && title !== '') {
              transactionLogin('', title);
          }
         return false;
      });

      $('.list-item .item-delete').on('click', function(){
          var _this = $(this);
          if ($(this).hasClass('active')) {

          } else {

              var count = $('.ajaxModal').length;
              if (count > 0) {
                $('#ajaxModal' + (count - 1)).toggleClass('in', false);
              }
              var $remote = "delete_confirmation.html"
                , $modal = $('<div class="modal fade ajaxModal" id="ajaxModal' + $('.ajaxModal').length + '"><div class="modal-body"></div></div>');
              $('body').append($modal);
              $modal.modal();

              $modal.on('returnTrue', function() {
                  _this.addClass('active');
                  _this.click();
                  setTimeout(function(){
                      _this.parents(".panel.list-item").remove();
                  }, 500);
                  pageNotification('success', 'You have successully deleted an item (Ref: 12345678)');

                  var offset = _this.closest('.list-item').find('input[name="post[]"]:checked').length;
                  var checked = $('input[name="post[]"]:checked').length - offset;
                  if (checked > 0) {
                      $('#selected-account').text(checked);
                  }
                  $('#footer-action').toggleClass('hide', checked === 0);
                  $('#footer-action .link-single').toggleClass('hide', checked !== 1);
              });

              $modal.on('returnFalse', function() {
              });

              $modal.on('hidden.bs.modal', function(e) {
                $modal.remove();
                if (count > 0) {
                  $('#ajaxModal' + (count - 1)).toggleClass('in', true);
                }
              });
              $modal.load($remote, function(){
                  modalReset($modal.find('.modal-dialog'));
              });

              return false;
          }

      });

      $('.list-item .item-transaction-delete').on('click', function(){
//          var _this = $(this);
//          if ($(this).hasClass('active')) {
//
//          } else {
//
//              var count = $('.ajaxModal').length;
//              if (count > 0) {
//                $('#ajaxModal' + (count - 1)).toggleClass('in', false);
//              }
//              var $remote = "delete_transaction_confirmation.html"
//                , $modal = $('<div class="modal fade ajaxModal" id="ajaxModal' + $('.ajaxModal').length + '"><div class="modal-body"></div></div>');
//              $('body').append($modal);
//              $modal.modal();
//
//              $modal.on('returnTrue', function() {
//                  _this.addClass('active');
//                  _this.click();
//                  setTimeout(function(){
//                      _this.parents(".panel.list-item").remove();
//                  }, 500);
//                  pageNotification('success', 'You have successully deleted an item (Ref: 12345678)');
//
//                  var offset = _this.closest('.list-item').find('input[name="post[]"]:checked').length;
//                  var checked = $('input[name="post[]"]:checked').length - offset;
//                  if (checked > 0) {
//                      $('#selected-account').text(checked);
//                  }
//                  $('#footer-action').toggleClass('hide', checked === 0);
//                  $('#footer-action .link-single').toggleClass('hide', checked !== 1);
//              });
//
//              $modal.on('returnFalse', function() {
//              });
//
//              $modal.on('hidden.bs.modal', function(e) {
//                $modal.remove();
//                if (count > 0) {
//                  $('#ajaxModal' + (count - 1)).toggleClass('in', true);
//                }
//              });
//              $modal.load($remote, function(){
//                  modalReset($modal.find('.modal-dialog'));
//              });
//
//              return false;
//          }

      });

      $('.nav-tabs').on('click', 'li > a', function(){
          setTimeout(sameHeight, 1);
          setTimeout(footerSet, 1);
      });
      sameHeight();

      $('a[data-edit]').on('click', function(){
          edit_id = $(this).attr('data-edit');
      });

      $('.account-select').on('change', function(){
        if ($(this).val() !== '') {
            setCurrency($(this).closest('.rows').find('.account-balance .balance-value'), $(this).val());
            $(this).closest('.rows').find('.account-balance').removeClass('hidden');
        } else {
            $(this).closest('.rows').find('.account-balance').addClass('hidden');
        }
      });

      $('.charge-select').on('change', function(){
        if ($(this).val() !== '') {
            $(this).closest('.rows').find('.account-charges').removeClass('hidden');
        } else {
            $(this).closest('.rows').find('.account-charges').addClass('hidden');
        }
      });

      $('.select-date-range').on('change', function(){
          var val = $(this).val();
          $('.date-range').toggleClass('hidden', val !== 'Date Range');
          $('.today').toggleClass('hidden', val !== 'Today');
          $('.current-month').toggleClass('hidden', val !== 'Current Month');
          $('.previous-month').toggleClass('hidden', val !== 'Previous Month');
      });

      $('.amount').on('keyup', function(){
          var total_amount = 0;
          $('.amount').each(function(){
              if (!isNaN($(this).val()) && $(this).val() !== '') {
                  total_amount += parseFloat($(this).val());
              }
          });

          setCurrency($('.total-amount'), total_amount.toFixed(2));
      });


      footerSet();

      $(document).on('click', '.modal-dialog .btn-primary, .accordion-toggle, #btn-sidebar, [href="#nav"]', function(){
          var timer = 1;
          if ($(this).hasClass('accordion-toggle') || $(this).hasClass('btn-primary')) {
              timer = 200;
          }
          setTimeout(footerSet, timer);

          if ($(this).hasClass('btn-primary')) {
              setTimeout(footerSet, timer + 5500);
          }
      });

      $('.btn-logout').on('click', function(){
         fader();
          setTimeout(function(){
              window.location.href = "index-2.html#logged-out";
          }, 500);
      });

      $(document).on('click', '.state, .stateful', function(){
         if ($(this).hasClass('active')) {
             if ($(this).hasClass('state')) {
                $('.state.active').removeClass('active');
             }
             if ($(this).hasClass('stateful')) {
                return;
             }
             $(this).removeClass('active');
         } else {
             if ($(this).hasClass('state')) {
                 $('.state.active').removeClass('active');
             }
             if ($(this).hasClass('stateful')) {
                 $(this).parent().find('.stateful').removeClass('active');
             }
             $(this).addClass('active');
         }
      });

      $('#form-page').on('submit', function(){
          var title = $(this).data('title');
          $('#main-body-content').scrollTop(0);
          submitModal(true, 'Your have successfully updated your ' + title + " (Ref: 12345678)");
          return false;
      });

      $(".bank-selection").on('focus', function(){

      });

      $("input[name=frequency-monthly]").on('change', function(){
          if ($(this).is(':checked')) {
              $('.frequency-monthly').removeClass('hidden');
              $('.frequency-monthly input, .frequency-monthly select').attr('data-required', true);
          } else {
              $('.frequency-monthly').addClass('hidden');
              $('.frequency-monthly input, .frequency-monthly select').attr('data-required', false);
              $('.frequency-monthly input, .frequency-monthly select').removeClass('parsley-validated').removeClass('parsley-error');

          }
      });

      $("input[name=investment-type]").on('change', function(){
          if ($(this).val() === 'CPFOA' || $(this).val() === 'SRS') {
              $('.cpfoa').removeClass('hidden');
              $('.cpfoa input').attr('data-required', true);

              $('.cash').addClass('hidden');
              $('.cash input').attr('data-required', false);
              $('.cash input').removeClass('parsley-validated').removeClass('parsley-error');
          } else {
              $('.cash').removeClass('hidden');
              $('.cash input').attr('data-required', true);

              $('.cpfoa').addClass('hidden');
              $('.cpfoa input').attr('data-required', false);
              $('.cpfoa input').removeClass('parsley-validated').removeClass('parsley-error');
          }
      });
      // WIDGETS VIEW DETAILS
      $(document).on('click','.currency-details-popup',function(e){
      		e.preventDefault();
      		if(showUpPopupModal){
            	showUpPopupModal('currency-details-select.html');
        	}
      });
      $(document).on('click','.unit-trust-details-popup',function(e){
      		e.preventDefault();
      		if(showUpPopupModal){
            	showUpPopupModal('unit-trust-details-select.html');
        	}
      });
      // NEW SELECTION REPLACTING
      $(".dropdown-special li a").on('click', function(e) {
    		e.preventDefault();
    		var val = $(this).text();
    		var parent = $(this).closest('.dropdown-special');
    		parent.find('.dropdown-label').html(val);

    		var field = parent.next('select');
    		field.find('option').each(function(){
    			if($(this).text() === val){
    				field[0].selectedIndex = $(this).index();
    				field.trigger('change');
    			}
    		});
  	   });

  });
}(jQuery);

var widgetAccordionReset = function($this) {
    var topbar = 0;
//    if ($this.hasClass('noTopBar')) {
//        topbar = 45;
//    }

    setTimeout(function(){
        var h_sidebar = $('#sidebar').outerHeight(),
            h_custom_widget = $('#customise-widgets').outerHeight(),
            wd_items = 0;

        $('#acc-widgets .panel-default > a').each(function(){
            wd_items = wd_items + $(this).outerHeight() + 1;
        });

        $('#acc-widgets .panel-default > a').attr('data-height', (h_sidebar - h_custom_widget - wd_items - topbar));
        $('#acc-widgets .panel-collapse.collapse.in').height((h_sidebar - h_custom_widget - wd_items - topbar));
//              $('#acc-widgets .panel-collapse').height(h_sidebar - h_custom_widget - wd_items);
    }, 1);

    if (Modernizr.tablet) {
        $('#nav').addClass('nav-xs');
    }
}

var gotoNextStep = function(goto) {
	$('.popup-step').addClass('hidden');
	$('.popup-step.popup-' + goto).removeClass('hidden');
};

var gotoNextFormStep = function($parent, goto) {
    if ($parent !== undefined){
        $parent.find('.popup-step').addClass('hidden');
        $parent.find('.popup-step.popup-' + goto).removeClass('hidden');
    }
};

var submitModal = function(notification, msg) {
    $('.modal-header .close').click();
    if (notification) {
        pageNotification('success', msg);
    }
}

var pageNotification = function(type, msg) {

    $('.scrollable.wrapper').scrollTop(0);
    $('.page-notification-msg .alert').removeClass('alert-success alert-info alert-danger');

    $('.page-notification-msg .alert').addClass('alert-' + type);

    $('.page-notification-msg .n-msg').html(msg);
    $('.page-notification-msg').removeClass('hidden');

    setTimeout(function(){
        $('.page-notification-msg').fadeOut();
        setTimeout(function(){
            $('.page-notification-msg').addClass('hidden');
            $('.page-notification-msg').css('display', '');
            footerSet();
        }, 1000);
    }, 5000);
}

var modalNotification = function(type, msg) {
    $('.modal-dialog .alert').removeClass('alert-success alert-info alert-danger');

    $('.modal-dialog .alert').addClass('alert-' + type);

    $('.modal-dialog .alert .m-msg').html(msg);
    $('.modal-notification').removeClass('hidden');
    setTimeout(function(){
        $('.modal-notification').fadeOut();
        setTimeout(function(){
            $('.modal-notification').addClass('hidden');
            $('.modal-notification').css('display', '');
        }, 1000);
    }, 5000);
}

var modalReset = function($elem) {
    if (!Modernizr.mobile) {
        $elem.css('margin-top','');


        var elementHeight = $elem.height();

        if ($(window).height() < (elementHeight + 100)) {
            $elem.addClass('modal-scrollable');
        } else {
            $elem.css('margin-top', '-' + (elementHeight/2) + 'px');
        }
    }
}

var sameHeight = function() {
    var dataSet = [];
    $('.uniform-height').css('height', '');
    $('.uniform-height').each(function(){
        var ds = $(this).attr('data-set');
        if (jQuery.inArray(ds, dataSet) < 0) {
            dataSet.push(ds);
        }
    });

    for (var i = 0; i < dataSet.length; i++) {
        var h = 0, o = 0;
        $('[data-set="' + dataSet[i] + '"]').each(function(){
            if (h <= $(this).outerHeight()) {
                h = $(this).outerHeight();
            }

            if (o <= ($(this).outerHeight() - $(this).height())) {
                o = ($(this).outerHeight() - $(this).height());
            }
        });
//        console.log(h,o,dataSet[i]);
        $('[data-set="' + dataSet[i] + '"]').height(h - o);

    }
}

var footerSet = function() {
    if ($('.page-footer').offset() !== undefined) {
        $('.page-footer').css({'position':'','bottom':''});
        //console.log($('.page-footer').offset().top + $('.scrollable.wrapper').scrollTop(), $(window).height());
        if (($('.page-footer').offset().top + $('.scrollable.wrapper').scrollTop()) < ($(window).height() - ($('.page-footer').height() + 50))) {
            $('.page-footer').css({'position':'absolute','bottom':0});
        } else {
            $('.page-footer').css({'position':'','bottom':''});
        }
    }
}

var loader = function(state) {
    if (!state && state !== undefined) {
        $('.loader').removeClass('in');
        $('.loader-backdrop-sm').removeClass('in');
        $('.loader-backdrop').removeClass('in');
        $('.loader-text').removeClass('in');

        setTimeout(function(){
            $('.loader').remove();
            $('.loader-backdrop-sm').remove();
            $('.loader-backdrop').remove();
            $('.loader-text').remove();
        },150);
        return false;

    } else {
        $('.loader-backdrop').remove();
        var $loader = $('<div class="loader fade"><div></div><div></div><div></div><div></div></div>'),
            $loader_backdrop_sm = $('<div class="loader-backdrop-sm fade"></div>'),
            $loader_backdrop = $('<div class="loader-backdrop fade"></div>'),
            $loader_text = $('<div class="loader-text fade"></div>');

        $('body').append($loader);
        $('body').append($loader_backdrop);
        $('body').append($loader_backdrop_sm);
        $('body').append($loader_text);

        $loader.show();
        $loader_backdrop_sm.show();
        $loader_backdrop.show();
        $loader_text.show();
        setTimeout(function(){
            $loader.addClass('in');
            $loader_backdrop_sm.addClass('in');
            $loader_backdrop.addClass('in');
            $loader_text.addClass('in');
        },10);

        return true;
    }
}

var fader = function(state) {
    if (!state && state !== undefined) {
        $('#fader').removeClass('in');

        setTimeout(function(){
            $('#fader').remove();
        },150);
        return false;

    } else {
        $('#loader').remove();
        var $fader = $('<div id="fader" class="fade"></div>');

        $('body').append($fader);

        $fader.show();
        setTimeout(function(){
            $fader.addClass('in');
        },10);

        return true;
    }
}

var setCurrency = function($elem, value){
    var money = value.split('.'),
        val = money[0].split(''),
        cent = money[1];
    var n = 0,
        amount = '';
    while(n < val.length) {
        if ((n % 3) === 0 && n !== 0) {
            amount = ',' + amount;
        }
        amount = val[val.length - n - 1] + '' + amount;
        n++;
    }

    if (cent === undefined) {
        cent = '00';
    }
    $elem.html('<span class="currency small-cr">' + amount + '.<span class="cent">' + cent + '</span></span> SGD');
}

var showPopNav = function($this){
    $this.addClass('active');
    if ($("#pop-nav").css('display') === 'none' && !$('#nav').hasClass('nav-xs')) {
        $("#pop-nav").css('left', ($this.offset().left + $this.width()))
        $("#pop-nav").stop(true, true).fadeIn();
    }
}

var closePopNav = function(){
    $('.level-one li.activate').removeClass('active');
    $("#pop-nav").stop(true, true).fadeOut();
    return false;
}



var edit_id = 0,
    modal_title = '',
    modal_elem = '',
    modal_action = '';



var transactionLogin = function($elem, title, action){
    modal_title = title;
    modal_elem = $elem;
    modal_action = action;
    $('#transaction-login').click();
}

var showUpPopupModal = function(remoteLink){
        var $remote = remoteLink,
            $modal  = $('<div class="modal fade ajaxModal" id="ajaxModal0"><div class="modal-body"></div></div>');
        $('body').append($modal);
        $modal.modal();
        $modal.load($remote, function(){
            modalReset($modal.find('.modal-dialog'));
        });
    };

var global = {};

function clickIE4(){
    if (event.button==2){
    return false;
    }
}
function clickNS4(e){
    if (document.layers||document.getElementById&&!document.all){
                   if (e.which==2||e.which==3){
                             return false;
                   }
           }
}
if (document.layers){
    document.captureEvents(Event.MOUSEDOWN);
    document.onmousedown=clickNS4;
}

else if (document.all&&!document.getElementById){
    document.onmousedown=clickIE4;
                document.onmouseup=clickLC;
                document.oncontextmenu=clickRC;
}
document.oncontextmenu=new Function("return false;");

$('#user_profile').on('hide.bs.dropdown',function(){
	$(this).find('.dropdown-menu').hide();
	$(this).removeClass('active');
});


$("a#nav-footer-toggle").on("click",function(){
	//$('i.uob-dashboard').trigger("click");
});





